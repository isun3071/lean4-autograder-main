import Lean
import AutograderLib
-- Ensures Mathlib is compiled when the container is being uploaded:
-- import Mathlib
open Lean IO System Elab Command Meta Lean.Meta Lean.Elab.Tactic

-- Don't change these
def agPkgPathPrefix : FilePath := ".lake" / "packages" / "autograder"
def solutionDirName := "AutograderTests"
def submissionUploadDir : FilePath := "/autograder/submission"
def resultsJsonPath : FilePath := ".." / "results" / "results.json"
-- These are arbitrary
def solutionModuleName := "Solution"
def submissionFileName := "Assignment.lean"

-- These are generated based on the above
def sheetModuleName := s!"{solutionDirName}.{solutionModuleName}".toName
def sheetFileName := s!"{solutionModuleName}.lean"
-- ".lake/packages/autograder/AutograderTests/AutograderTests.Solution.lean"
def sheetFile : FilePath := agPkgPathPrefix / solutionDirName / sheetFileName

/-! ## Comparator scratch space

Grading verdicts are produced by [Comparator](https://github.com/leanprover/comparator),
which independently rebuilds the relevant declarations in a sandboxed subprocess,
re-serializes them through `lean4export`, and replays them through the Lean kernel,
rather than trusting our own in-process elaboration of the submission the way this
autograder used to. `ComparatorGrading` is a scratch Lake library, regenerated on
every grading run, holding:

* `Ref.lean` -- a verbatim copy of the sheet, wrapped in a namespace so its
  declarations are reachable under a qualified name that can never collide with a
  submission's own declarations of the same (bare) name.
* `Solution.lean` -- whatever is being graded (the submission, or a `--test`
  fixture), verbatim. Used directly as `solution_module` for proof exercises.
* `ChallengeN.lean` / `PinN.lean` (one numbered pair per definition exercise) --
  `ChallengeN` holds a trivial (`rfl`-provable) reference "pin" theorem; `PinN`
  imports `Solution` and restates the same pin theorem for whatever the
  submission actually provided. Each definition exercise gets its own pair of
  *separate modules* rather than sharing one file: Lean's compilation is
  whole-file, so if one exercise's pin theorem is genuinely unprovable (an
  expected, normal outcome for a wrong submission), that must not fail the
  build of -- and thus cascade into rejecting -- every other exercise that
  happens to share the file.
-/

def comparatorLibDirName := "ComparatorGrading"
def comparatorLibDir : FilePath := agPkgPathPrefix / comparatorLibDirName
def comparatorRefFile : FilePath := comparatorLibDir / "Ref.lean"
def comparatorSolutionFile : FilePath := comparatorLibDir / "Solution.lean"
def comparatorConfigFile : FilePath := comparatorLibDir / "config.json"
def comparatorRefModule := s!"{comparatorLibDirName}.Ref"
def comparatorSolutionModule := s!"{comparatorLibDirName}.Solution"
def comparatorReferenceNamespace := "ComparatorReference"
def comparatorBinary : FilePath :=
  ".lake" / "packages" / "comparator" / ".lake" / "build" / "bin" / "comparator"
def lean4exportBinary : FilePath :=
  ".lake" / "packages" / "lean4export" / ".lake" / "build" / "bin" / "lean4export"
def fakeLandrunScript : FilePath :=
  ".lake" / "packages" / "comparator" / "scripts" / "fake-landrun.sh"

def comparatorPinChallengeFile (i : Nat) : FilePath := comparatorLibDir / s!"Challenge{i}.lean"
def comparatorPinChallengeModule (i : Nat) : String := s!"{comparatorLibDirName}.Challenge{i}"
def comparatorPinFile (i : Nat) : FilePath := comparatorLibDir / s!"Pin{i}.lean"
def comparatorPinModule (i : Nat) : String := s!"{comparatorLibDirName}.Pin{i}"

-- Used for non-exercise-specific results (e.g., global failures)
structure FailureResult where
  output : String
  score : Float := 0.0
  output_format : String := "text"
  deriving ToJson

-- Used for exercise-specific results
structure ExerciseResult where
  name : Name
  score : Float
  status : String
  output : String
  deriving ToJson

def ExerciseResult.print (er : ExerciseResult) : IO Unit := do
  let score :=
    match JsonNumber.fromFloat? er.score with
    | Sum.inl e => Json.str e
    | Sum.inr n => Json.num n
  IO.println s!"{er.name}:"
  IO.println s!"  {er.status} ({score} points)"
  IO.println s!"  {er.output}"

structure ExerciseResultDebug extends ExerciseResult where
  sheet_name : Name         -- Name of the exercise in the sheet
  expected_status : String  -- Expected status of the test, "passed" or "failed"
  output_log : String       -- Additional information about the autograder's decision

inductive Color : Type
  | red
  | green

def addANSICode (c : Color) (s : String) : String :=
  let code := match c with
    | .red => "31"
    | .green => "32"
  s!"\x1b[1m[{code}m{s}[0m"

def ExerciseResultDebug.print (er : ExerciseResultDebug) : IO Unit := do
  IO.print s!"{er.name}: "
  if er.status == er.expected_status then
    IO.println (addANSICode Color.green "Passed")
  else
    IO.println (addANSICode Color.red "Failed")
  IO.println s!"  {er.output_log}"

structure GradingResults where
  tests : Array ExerciseResult
  output: String
  output_format: String := "text"
  deriving ToJson

def GradingResults.print (gr : GradingResults) : IO Unit := do
  IO.println gr.output
  for er in gr.tests do
    er.print
    IO.println ""

def Lean.Environment.moduleDataOf? (module : Name) (env : Environment)
  : Option ModuleData := do
  let modIdx : Nat ← env.getModuleIdx? module
  env.header.moduleData[modIdx]?

def Lean.Environment.moduleOfDecl? (decl : Name) (env : Environment)
  : Option Name := do
  let modIdx : Nat ← env.getModuleIdxFor? decl
  env.header.moduleNames[modIdx]?

def defaultValidAxioms : Array Name :=
  #["Classical.choice".toName,
    "Quot.sound".toName,
    "propext".toName,
    "funext".toName]

-- Ideally, we could format our Gradescope output nicely as HTML and escape
-- inserted file names/error messages/etc. Unfortunately, Gradescope doesn't
-- handle pre-escaped HTML well (it tries to re-escape it), so until a
-- workaround for that issue is found, we'll stick with plain text.
def escapeHtml (s : String) :=
  [("<", "&lt;"), (">", "&gt;"), ("&", "&amp;"), ("\"", "&quot;")].foldl
    (λ acc (char, repl) => acc.replace char repl) s

-- Throw error and show it to the student, optionally providing additional
-- information for the instructor only
-- TODO this fails with --local if ../results doesn't exist
def exitWithError {α} (errMsg : String) (instructorInfo: String := "")
  : IO α := do
  let result : FailureResult := {output := errMsg}
  -- Outside a real Gradescope container (e.g. local dev testing outside `--local`'s
  -- own results-printing path, or an error raised before we even know we're in
  -- `--local` mode, like a bad CLI argument), `../results` won't exist. Don't let
  -- that write failure mask the actual error below with a confusing, unrelated
  -- "no such file or directory" instead.
  try
    IO.FS.writeFile resultsJsonPath (toJson result).pretty
  catch _ => pure ()
  throw <| IO.userError (errMsg ++ "\n" ++ instructorInfo)

/-- Axioms declared in the sheet and tagged `@[legalAxiom]`, in addition to whatever
`@[validAxioms]` specifies for `name` (or `defaultValidAxioms` if unspecified). This is
the `permitted_axioms` list handed to Comparator. Comparator independently enforces
both that only these axioms are used *and* (since it structurally compares every
permitted axiom's declaration between challenge and solution) that a submission can't
smuggle in its own same-named axiom with a different, exploitable type. -/
def legalAxiomNames (sheet : Environment) : Array Name :=
  sheet.constants.toList.filterMap (fun (n, info) =>
    match info with
    | .axiomInfo _ => if legalAxiomAttr.hasTag sheet n then some n else none
    | _ => none) |>.toArray

def permittedAxiomsFor (sheet : Environment) (name : Name) : Array Name :=
  let validAxioms :=
    if let some t := validAxiomsAttr.getParam? sheet name then t
    else defaultValidAxioms
  validAxioms ++ legalAxiomNames sheet

structure ComparatorConfig where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Array String := #[]
  permitted_axioms : Array String
  enable_nanoda : Bool := false
  deriving ToJson

/-- Splits off the leading `import` lines of a trusted (instructor-authored) Lean
source file, so the remainder can be re-wrapped in a namespace. This is purely
textual (not parser-driven), which is fine here since it is only ever applied to
trusted sheet content, never to a submission. -/
def splitLeadingImports (contents : String) : String × String :=
  let isHeaderLine (s : String) : Bool :=
    let t := s.trimAscii.copy
    t.isEmpty || t.startsWith "import " || t == "import"
  let lines := contents.splitOn "\n"
  let (headerLines, rest) := lines.span isHeaderLine
  (String.intercalate "\n" headerLines, String.intercalate "\n" rest)

/-- Writes `ComparatorGrading/Ref.lean`: the sheet's own imports, followed by a
verbatim copy of the rest of the sheet wrapped in `namespace ComparatorReference`. -/
def writeComparatorRef (sheetContents : String) : IO Unit := do
  let (imports, body) := splitLeadingImports sheetContents
  IO.FS.createDirAll comparatorLibDir
  IO.FS.writeFile comparatorRefFile <|
    imports ++ "\n\nnamespace " ++ comparatorReferenceNamespace ++ "\n"
      ++ body ++ "\n\nend " ++ comparatorReferenceNamespace ++ "\n"

/-- Writes `ComparatorGrading/Solution.lean`: whatever is being graded (submission or
`--test` fixture), verbatim -- deliberately *not* importing `ComparatorGrading.Ref`.
Solution.lean never itself references `ComparatorReference.*` (only `PinN.lean` does,
and it already imports `Ref` directly); importing it here anyway would leak the sheet's
own `notation`/`macro` declarations into the submission's scope, since those aren't
namespace-scoped the way ordinary declarations are -- even though `Ref.lean` wraps the
sheet in `namespace ComparatorReference`. A submission that (legitimately or
maliciously) redeclares the same notation would then collide with the sheet's own
copy, breaking the whole shared file instead of just the one exercise. -/
def writeComparatorSolution (bodyContents : String) : IO Unit := do
  IO.FS.createDirAll comparatorLibDir
  IO.FS.writeFile comparatorSolutionFile bodyContents

/-- One "pin" obligation: verify that `subName` (as it appears in whatever is being
graded -- the submission, or a `--test` candidate) is provably equal to the sheet's
reference declaration `refName`. -/
structure PinTarget where
  subName : Name
  refName : Name
  /-- Pretty-printed type of `refName` (fully-qualified names/universes, so it
  doesn't depend on any `open`/notation state), used to give the *challenge*-side
  alias `def subName : refTypeText := ComparatorReference.refName` an explicit
  type ascription. Without this, a polymorphic `refName` (leading implicit
  arguments) can't be aliased point-free -- Lean eagerly tries to instantiate the
  leading implicit as soon as the identifier appears unapplied, instead of
  generalizing it back into the alias's own signature. -/
  refTypeText : String
  /-- Safety keyword needed for the alias to type-check; must match `refName`'s
  own safety. -/
  safetyKeyword : String

def pinTheoremName (t : PinTarget) : String := s!"{t.subName}__pin"

/-- The pin theorem states `@subName = @refName` (all arguments explicit via `@`)
rather than the bare `subName = refName`, for the same reason the challenge-side
alias needs a type ascription: with a polymorphic (implicit-argument) `subName`,
`Eq`'s own implicit type argument can't be inferred from two unapplied,
still-polymorphic terms. `@` gives both sides a concrete, closed type. -/
def pinTheoremStatement (t : PinTarget) : String :=
  s!"@{t.subName} = @{comparatorReferenceNamespace}.{t.refName}"

/-- Content of `ChallengeN.lean`: a reference-forwarding alias plus the (trivially
true, proved by `rfl`) pin theorem, giving Comparator a same-named, same-typed
statement on the trusted side to structurally compare the submission's own pin
theorem against. -/
def PinTarget.challengeContent (t : PinTarget) : String :=
  s!"import {comparatorRefModule}\n\n" ++
  s!"{t.safetyKeyword}def {t.subName} : {t.refTypeText} := {comparatorReferenceNamespace}.{t.refName}\n" ++
  s!"theorem {pinTheoremName t} : {pinTheoremStatement t} := by rfl\n"

/-- Content of `PinN.lean`: imports the (already-built) `Solution` module for
`t.subName`, then restates the pin theorem with `tacticBlock` as its proof. -/
def PinTarget.solutionContent (t : PinTarget) (tacticBlock : String) : String :=
  s!"import {comparatorRefModule}\nimport {comparatorSolutionModule}\n\n" ++
  s!"theorem {pinTheoremName t} : {pinTheoremStatement t} := by\n" ++ tacticBlock

def safetyKeywordFor (info : ConstantInfo) : String :=
  if info.isUnsafe then "unsafe " else if info.isPartial then "partial " else ""

/-- Pretty-prints `t` (a type) using fully-qualified names and explicit universes,
so the result doesn't depend on any `open`/notation state and can be spliced
directly into a freshly-generated file as a type ascription. -/
def renderType (sheet : Environment) (t : Expr) : IO String := do
  let ctx : Core.Context := { fileName := "", fileMap := default }
  let cstate : Core.State := { env := sheet }
  let helper : MetaM String :=
    withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.universes true) do
      return (← Meta.ppExpr t).pretty
  let (s, _, _) ← MetaM.toIO helper ctx cstate
  return s

/-- Writes the `ChallengeN.lean`/`PinN.lean` pair for one definition exercise. -/
def writeComparatorPin (i : Nat) (t : PinTarget) (tacticBlock : String) : IO Unit := do
  IO.FS.createDirAll comparatorLibDir
  IO.FS.writeFile (comparatorPinChallengeFile i) t.challengeContent
  IO.FS.writeFile (comparatorPinFile i) (t.solutionContent tacticBlock)

/-- Set once, at the top of `main`, from `cfg.localRun`. Read by
`resolveLocalLandrunFallback` below; see its doc comment for why this is a ref rather
than a parameter threaded through the whole call chain down to `runComparator`. -/
initialize localRunRef : IO.Ref Bool ← IO.mkRef false

/-- Whether a landrun-compatible binary is resolvable right now: either
`COMPARATOR_LANDRUN` is already set (Comparator will use it directly, whatever it
points to -- an explicit choice we never override), or a bare `landrun` resolves via
`PATH`. -/
def landrunIsResolvable : IO Bool := do
  if (← IO.getEnv "COMPARATOR_LANDRUN").isSome then
    return true
  try
    let out ← IO.Process.output { cmd := "landrun", args := #["--version"] }
    return out.exitCode == 0
  catch _ => return false

/-- Whether `resolveLocalLandrunFallback` has already printed its warning this run, so
it only prints once (it's otherwise called once per Comparator invocation, i.e. once
per exercise). -/
initialize landrunFallbackWarnedRef : IO.Ref Bool ← IO.mkRef false

/-- In `--local` mode only -- never during a real Gradescope run, where `setup.sh`
guarantees a real, sandboxing `landrun` is on `PATH`, and where silently degrading
sandboxing would be a serious problem, not a convenience -- fall back to Comparator's
own `scripts/fake-landrun.sh` dev shim (which provides NO sandboxing at all) when
neither `COMPARATOR_LANDRUN` nor a bare `landrun` resolves. This exists so `lake exe
autograder --local ...` works out of the box for course staff iterating on a stencil,
who would otherwise see every single exercise fail with a misleading "could not be
built" message and no indication that the actual problem is an unrelated missing
binary. Returns the env override to hand to `runComparator`, if any; prints a loud
warning the first time it activates. -/
def resolveLocalLandrunFallback : IO (Array (String × Option String)) := do
  if !(← localRunRef.get) then return #[]
  if ← landrunIsResolvable then return #[]
  let alreadyWarned ← landrunFallbackWarnedRef.get
  landrunFallbackWarnedRef.set true
  if ← fakeLandrunScript.pathExists then
    if !alreadyWarned then
      IO.println <| "WARNING: `landrun` was not found on PATH and COMPARATOR_LANDRUN is "
        ++ "not set. Falling back to Comparator's scripts/fake-landrun.sh dev shim for "
        ++ "this --local run, which provides NO SANDBOXING. This is fine for locally "
        ++ "testing your own stencil/submission files, but must never be relied on to "
        ++ "grade an untrusted submission -- install a real `landrun` (or point "
        ++ "COMPARATOR_LANDRUN at one) for that."
    return #[("COMPARATOR_LANDRUN", some fakeLandrunScript.toString)]
  else
    if !alreadyWarned then
      IO.println <| "WARNING: `landrun` was not found on PATH, COMPARATOR_LANDRUN is "
        ++ "not set, and Comparator's dev shim isn't available either (expected at "
        ++ s!"{fakeLandrunScript}). Comparator will fail to run."
    return #[]

def comparatorRunEnv : IO (Array (String × Option String)) := do
  let lean4export ← IO.FS.realPath lean4exportBinary
  let landrunFallback ← resolveLocalLandrunFallback
  return #[("COMPARATOR_LEAN4EXPORT", some lean4export.toString)] ++ landrunFallback

/-- Runs `comparator` on `cfg` and returns whether it succeeded, plus a log of its
output for debugging/instructor info. -/
def runComparator (cfg : ComparatorConfig) : IO (Bool × String) := do
  IO.FS.writeFile comparatorConfigFile (toJson cfg).pretty
  let comparatorPath ← IO.FS.realPath comparatorBinary
  let env ← comparatorRunEnv
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", comparatorPath.toString, comparatorConfigFile.toString]
    env
  }
  return (out.exitCode == 0, out.stdout ++ "\n" ++ out.stderr)

/-- Coarse categorization of why Comparator rejected a submission, derived by pattern
matching against its own diagnostic output (`Comparator/Compare.lean`,
`Comparator/Axioms.lean`, `Main.lean` in the pinned Comparator version). This is a
best-effort enrichment of the student-facing message, never a correctness dependency:
Comparator's exact wording is an internal implementation detail that could change in a
future version, and any log that doesn't match a known pattern always falls back to
`.unknown`, which reproduces today's generic message. -/
inductive ComparatorFailureReason
  | usesSorry
  | illegalAxiom (axiomName : String)
  | wrongStatement
  | kernelRejected
  | buildFailed
  | unknown

/-- Pulls the axiom name out of Comparator's `Illegal axiom detected: 'name'` message. -/
def extractIllegalAxiomName (log : String) : Option String := do
  let parts := log.splitOn "Illegal axiom detected: '"
  let rest ← parts[1]?
  let name := (rest.splitOn "'").headD ""
  if name.isEmpty then none else some name

def classifyComparatorFailure (log : String) : ComparatorFailureReason :=
  if let some axiomName := extractIllegalAxiomName log then
    if axiomName == "sorryAx" then .usesSorry else .illegalAxiom axiomName
  else if #["theorem statement do not match", "constant kind don't match",
      "does not match between challenge and target", "is not a theorem",
      "is not a definition"].any (fun needle => (log.splitOn needle).length > 1) then
    .wrongStatement
  else if (log.splitOn "Child exited with").length > 1 then
    .buildFailed
  else if (log.splitOn "Running Lean default kernel on solution").length > 1
      && (log.splitOn "Lean default kernel accepts the solution").length == 1 then
    .kernelRejected
  else
    .unknown

def proofFailureMessage : ComparatorFailureReason → String
  | .usesSorry => "Your proof is missing or incomplete (it appears to use `sorry`)."
  | .illegalAxiom ax =>
    s!"Your proof relies on the axiom `{ax}`, which isn't permitted for this exercise."
  | .wrongStatement => "Your proof does not prove the expected statement for this exercise."
  | .kernelRejected => "Your proof was rejected by an independent kernel check."
  | .buildFailed => "Your submission could not be built for independent verification; "
      ++ "please check it for compile errors."
  | .unknown => "Comparator could not verify this proof. This usually means the proof is "
      ++ "missing, uses `sorry`, uses an axiom that isn't permitted, or doesn't prove the "
      ++ "expected statement."

def defFailureMessage : ComparatorFailureReason → String
  | .usesSorry => "Your definition could not be proven equal to the reference solution."
  | .illegalAxiom ax =>
    s!"Proving your definition equal to the reference solution relies on the axiom `{ax}`, "
      ++ "which isn't permitted for this exercise."
  | .wrongStatement => "Your definition's type does not match the expected type for this exercise."
  | .kernelRejected => "The proof that your definition equals the reference solution was "
      ++ "rejected by an independent kernel check."
  | .buildFailed => "Your submission could not be built for independent verification; "
      ++ "please check it for compile errors."
  | .unknown => "Comparator could not verify this definition against the reference solution."

/-- Verifies a proof exercise via Comparator. `challenge_module` is the sheet itself,
unmodified (its theorem statement -- `sorry`'d or not, Comparator never inspects the
proof body -- is the trusted reference); `solution_module` is the submission (or, in
`--test` mode with `subName ≠ name`, the submission plus a one-line proof-term
alias, already baked into `ComparatorGrading/Solution.lean` by the caller). -/
def verifyProofViaComparator (name subName : Name) (pts : Float)
    (sheet : Environment) : IO ExerciseResultDebug := do
  let cfg : ComparatorConfig := {
    challenge_module := sheetModuleName.toString
    solution_module := comparatorSolutionModule
    theorem_names := #[name.toString]
    permitted_axioms := (permittedAxiomsFor sheet name).map Name.toString
  }
  let (ok, log) ← runComparator cfg
  if ok then
    return { name := subName, score := pts, status := "passed",
             output := "Passed all tests", sheet_name := name,
             expected_status := "none",
             output_log := s!"Verified by Comparator\n{log}" }
  else
    return { name := subName, score := 0.0, status := "failed",
             output := proofFailureMessage (classifyComparatorFailure log),
             sheet_name := name, expected_status := "none",
             output_log := s!"Comparator rejected the proof\n{log}" }

/-- Verifies a definition exercise's pin theorem via Comparator: that `t.subName` has
the same type/universe levels/safety as the reference `t.refName` (`definition_names`),
and that the pin theorem proving them equal type-checks using only permitted axioms
(`theorem_names`). -/
def verifyDefViaComparator (i : Nat) (t : PinTarget) (pts : Float)
    (sheet : Environment) : IO ExerciseResultDebug := do
  let cfg : ComparatorConfig := {
    challenge_module := comparatorPinChallengeModule i
    solution_module := comparatorPinModule i
    theorem_names := #[pinTheoremName t]
    definition_names := #[t.subName.toString]
    permitted_axioms := (permittedAxiomsFor sheet t.refName).map Name.toString
  }
  let (ok, log) ← runComparator cfg
  if ok then
    return { name := t.subName, score := pts, status := "passed",
             output := "Passed all tests", sheet_name := t.refName,
             expected_status := "none",
             output_log := s!"Verified equal to reference by Comparator\n{log}" }
  else
    return { name := t.subName, score := 0.0, status := "failed",
             output := defFailureMessage (classifyComparatorFailure log),
             sheet_name := t.refName, expected_status := "none",
             output_log := s!"Comparator rejected the definition\n{log}" }

def tacticsFor (sheet : Environment) (name : Name) : Array Syntax :=
  let raw :=
    if let some t := validTacticsAttr.getParam? sheet name then t
    else if let some d := defaultTacticsAttr.getParam? sheet `setDefaultTactics then d
    else #[]
  raw.map Prod.snd

/-- Recovers the exact original source text of `stx` from `sourceContents`, via its
parsed position range -- *not* by pretty-printing, which does not reliably round-trip
(e.g. the `rfl` tactic's parsed syntax pretty-prints as the semantically different
`exact Iff.rfl`). -/
def syntaxSourceText (sourceContents : String) (stx : Syntax) : Option String := do
  let startPos ← stx.getPos?
  let endPos ← stx.getTailPos?
  let bytes := sourceContents.toUTF8
  return String.fromUTF8! (bytes.extract startPos.byteIdx endPos.byteIdx)

/-- Combines `rfl`, `apply HEq.refl`, every tactic configured via `@[validTactics]`/
`@[defaultTactics]` (recovered from the sheet's own source text, see
`syntaxSourceText`), and a final `sorry` fallback into one `first | ...` block,
spliced as a definition exercise's pin theorem proof.

Definition exercises are always verified by handing this block to Comparator and
letting its independent, from-scratch elaboration be the sole judge of whether any
alternative works, rather than pre-deciding locally which one "should" succeed: a
local pre-check would be unreliable, since whether e.g. `rfl` succeeds in proving two
independently-elaborated (even if source-identical) recursive definitions equal can
depend on low-level details of how the equation compiler happened to compile each
copy, which isn't guaranteed to transfer between our in-process environment and
Comparator's from-scratch rebuild.

The `sorry` fallback ensures a genuinely-unprovable pin theorem still produces a
clean Comparator axiom-check rejection (`sorryAx` is never a permitted axiom) instead
of a hard Lean compile error for the containing file/module. -/
def combinedTacticBlock (sheetContents : String) (tactics : Array Syntax) : String :=
  let tacticTexts := tactics.filterMap (syntaxSourceText sheetContents)
  let alternatives := #["rfl", "apply HEq.refl"] ++ tacticTexts ++ #["sorry"]
  "  first\n" ++ String.intercalate "\n" (alternatives.toList.map (s!"    | ({·})")) ++ "\n"

/-- Cheap, purely local precondition for a definition exercise (the declaration must
actually contain a value) so we can fail fast without invoking Comparator at all for
an obviously-incomplete submission. Type/universe/safety matching and the actual
equality proof are both independently verified by Comparator later. -/
def defQuickCheck (subName name : Name) (subConstInfo : ConstantInfo) :
    Option ExerciseResultDebug :=
  if !subConstInfo.hasValue then
    some { name := subName, score := 0.0, status := "failed",
           output := "Declaration does not contain a value",
           sheet_name := name, expected_status := "none",
           output_log := "Declaration does not contain a value" }
  else none

/-! ## Tactic allowlist enforcement

`@[autogradedProof]` checks only that a submission *closes the stated theorem* using
permitted axioms. It deliberately says nothing about how the proof was found, which is
usually right -- but not when an assignment exists to practice a specific technique.
Many propositional exercises fall to a one-word `grind` or `simp`, and those would
otherwise earn full marks while demonstrating none of the intended skill.

`@[allowedTactics]` on a sheet exercise restricts which tactics its proof may use. Two
properties matter for it to be enforcement rather than an honour-system nudge:

* **The check runs on a parse of the submission, not on its elaboration.** Elaborating a
  Lean file executes arbitrary code in this process (`initialize`/`#eval`/`run_cmd`
  blocks run during elaboration, which is exactly why `run_autograder` destroys the
  deploy key beforehand). Parsing executes none of it, so a submission cannot influence
  the verdict on itself.
* **Parsing uses the *sheet's* environment, never the submission's.** Which syntax is a
  tactic at all is therefore fixed by the instructor's imports. A submission cannot
  enlarge that set by declaring its own `syntax ... : tactic`, nor reach a tactic from a
  library the sheet does not import -- such a file simply fails to parse here, which is
  reported as a violation rather than quietly allowed.

It remains a *syntactic* check, and the honest limit is that it constrains tactics, not
proofs: a submission that writes the proof term directly, using no tactics at all, has
nothing for this to reject. Catching that needs a check on the elaborated term, which
is a different (and much harder to calibrate) mechanism -- see the README. -/

/-- Syntax node kinds registered in Lean's `tactic` parser category, according to `env`.

Testing membership here, rather than pattern-matching a hard-coded list of tactic names
or sniffing the kind's name for `.Tactic.`, is what makes the walk below complete: every
tactic is registered in this category, including ones defined by `macro`/`syntax`
declarations, so none is invisible to the allowlist. -/
def tacticKinds (env : Environment) : PersistentHashMap SyntaxNodeKind Unit :=
  match (Parser.parserExtension.getState env).categories.find? `tactic with
  | some cat => cat.kinds
  | none     => .empty

/-- The name a student would recognize a tactic node by: the keyword they typed.

Every tactic node's first child is an atom holding that keyword (`rewrite`, `rfl`,
`intro`), so this reports exactly what appears in the source. The fallback covers
infix combinators such as `<;>`, whose first child is a nested tactic rather than an
atom; those are named by the last component of their syntax kind. -/
def tacticDisplayName (stx : Syntax) : String :=
  match stx with
  | .node _ k args =>
    match args[0]? with
    | some (Lean.Syntax.atom _ v) => v
    | _ => (k.components.getLastD `unknown).toString
  | _ => "<malformed>"

/-- Every tactic node anywhere inside `stx`, outermost first.

Recursion continues *through* tactic nodes rather than stopping at them, so tactics
nested inside a combinator (`first | rfl | simp`, `try simp`, `rfl <;> simp`) are each
checked on their own. Both the combinator and its branches must be permitted. -/
partial def collectTactics (kinds : PersistentHashMap SyntaxNodeKind Unit)
    (stx : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  let acc := if kinds.contains stx.getKind then acc.push stx else acc
  stx.getArgs.foldl (fun a c => collectTactics kinds c a) acc

/-- The name a parsed command declares, if it declares one. -/
partial def declNameOf? (stx : Syntax) : Option Name :=
  if stx.getKind == ``Lean.Parser.Command.declId then
    some stx[0].getId
  else
    stx.getArgs.findSome? declNameOf?

/-- Splits `contents` into top-level commands, parsing only -- nothing is elaborated, so
none of the submission's own code runs. `env` supplies the syntax in scope and is always
the sheet's environment; see the note above. -/
def parseCommandsOnly (env : Environment) (contents fileName : String)
    : IO (Array Syntax) := do
  let ictx := Parser.mkInputContext contents fileName
  let (_, parserState, _) ← Parser.parseHeader ictx
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let mut cmds : Array Syntax := #[]
  let mut ps := parserState
  let mut msgs := MessageLog.empty
  while !ictx.atEnd ps.pos do
    let (stx, ps', msgs') := Parser.parseCommand ictx pmctx ps msgs
    -- A command that consumes nothing means the parser is stuck (an unparseable
    -- construct); stop rather than spin forever on it.
    if ps'.pos == ps.pos then break
    cmds := cmds.push stx
    ps := ps'
    msgs := msgs'
  return cmds

/-- Whether any part of `stx` failed to parse.

`parseCommandsOnly` uses the *sheet's* syntax, so a submission that declares its own
tactic (`macro "sneaky" : tactic => `(tactic| grind)`) leaves a hole here: the tactic is
real when the submission elaborates itself, but is not syntax we know, so it parses as
`missing`. That must be refused rather than silently contributing no tactic names to
check -- otherwise defining a macro would be a way to become invisible to the allowlist. -/
partial def containsMissing (stx : Syntax) : Bool :=
  match stx with
  | .missing      => true
  | .node _ _ args => args.any containsMissing
  | _             => false

/-- Whether `stx` contains a `by` block, i.e. is proved with tactics at all.

An exercise carrying `@[allowedTactics]` is asking the student to practice tactics, so a
term-mode proof (`:= fun h => h.1 h.2`) sidesteps the exercise entirely *and* offers the
allowlist nothing to inspect. Requiring a tactic block closes that, leaving the allowlist
itself to govern which tactics are then used. -/
partial def containsByBlock (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.byTactic
    || stx.getArgs.any containsByBlock

/-- Tactics used in `cmdStx` that `allowed` does not permit, deduplicated and in source
order. An empty array means the proof is within its budget. -/
def disallowedTactics (kinds : PersistentHashMap SyntaxNodeKind Unit)
    (allowed : Array String) (cmdStx : Syntax) : Array String :=
  (collectTactics kinds cmdStx).foldl (init := #[]) fun bad s =>
    let n := tacticDisplayName s
    if allowed.contains n || bad.contains n then bad else bad.push n

/-- Student-facing explanation of a tactic violation. It names both what was used and
what was permitted, so the student can correct the proof rather than guess. -/
def tacticViolationMessage (bad allowed : Array String) : String :=
  let list (a : Array String) := String.intercalate ", " (a.toList.map (s!"`{·}`"))
  s!"This exercise restricts which tactics you may use. Your proof uses "
    ++ s!"{list bad}, which " ++ (if bad.size == 1 then "is" else "are")
    ++ " not permitted here. Permitted tactics for this exercise: "
    ++ s!"{list allowed}."

def gradeSubmission (sheet submission : Environment)
    (sheetContents submissionContents : String) : IO (Array ExerciseResult) := do
  writeComparatorRef sheetContents
  writeComparatorSolution submissionContents

  let mut proofExercises : Array (Name × Float) := #[]
  let mut pinTargets : Array (Nat × PinTarget × Float) := #[]
  let mut immediateResults : Array ExerciseResult := #[]
  let mut nextIdx := 0

  -- Parse the submission once, up front, for `@[allowedTactics]` checking. This is a
  -- parse only: none of the submission's code runs, and the syntax in scope comes from
  -- the sheet, not the submission. Indexed by declared name so each exercise can be
  -- checked against the declaration that actually claims to answer it.
  let kinds := tacticKinds sheet
  let submissionCmds ← parseCommandsOnly sheet submissionContents submissionFileName
  let mut declCmds : Std.HashMap Name Syntax := ∅
  for cmd in submissionCmds do
    if let some n := declNameOf? cmd then
      declCmds := declCmds.insert n cmd

  for (name, constInfo) in sheet.constants.toList do
    if let some pts := autogradedProofAttr.getParam? sheet name then
      if not name.isInternal then
        if (submission.find? name).isSome then
          -- A tactic violation fails the exercise outright, before Comparator is
          -- consulted: the proof may well be valid, but it is not the proof this
          -- exercise asked for, so there is nothing for verification to settle.
          match allowedTacticsAttr.getParam? sheet name with
          | some allowed =>
            -- Every branch here fails closed: anything this check cannot fully see
            -- through is refused, never waved on.
            let verdict : Option String :=
              match declCmds[name]? with
              | none =>
                -- Elaboration found the declaration but our parse did not, so we have
                -- nothing to inspect.
                some ("Your proof of this exercise could not be checked against its "
                  ++ "permitted-tactic list, so it cannot be awarded credit. Submit the "
                  ++ "proof directly, as an ordinary theorem, rather than generating it.")
              | some cmd =>
                if containsMissing cmd then
                  some ("Your proof of this exercise uses syntax that is not available "
                    ++ "for this assignment, so it could not be checked against the "
                    ++ "permitted-tactic list. Do not define your own tactics or import "
                    ++ "libraries beyond the ones the assignment provides.")
                else if !containsByBlock cmd then
                  some ("This exercise must be solved with a tactic proof (`:= by ...`), "
                    ++ "using only its permitted tactics. Writing the proof term "
                    ++ "directly is not accepted here.")
                else
                  let bad := disallowedTactics kinds allowed cmd
                  if bad.isEmpty then none else some (tacticViolationMessage bad allowed)
            match verdict with
            | none => proofExercises := proofExercises.push (name, pts)
            | some output =>
              immediateResults := immediateResults.push
                { name, score := 0.0, status := "failed", output }
          | none => proofExercises := proofExercises.push (name, pts)
        else
          immediateResults := immediateResults.push
            { name, score := 0.0, status := "failed",
              output := "Declaration not found in submission" }
    else if let some pts := autogradedDefAttr.getParam? sheet name then
      if not name.isInternal then
        if let some subConstInfo := submission.find? name then
          if let some failure := defQuickCheck name name subConstInfo then
            immediateResults := immediateResults.push failure.toExerciseResult
          else
            let target : PinTarget :=
              { subName := name, refName := name,
                refTypeText := ← renderType sheet constInfo.type,
                safetyKeyword := safetyKeywordFor constInfo }
            let i := nextIdx
            nextIdx := nextIdx + 1
            writeComparatorPin i target (combinedTacticBlock sheetContents (tacticsFor sheet name))
            pinTargets := pinTargets.push (i, target, pts)
        else
          immediateResults := immediateResults.push
            { name, score := 0.0, status := "failed",
              output := "Declaration not found in submission" }

  let mut results := immediateResults
  for (name, pts) in proofExercises do
    let r ← verifyProofViaComparator name name pts sheet
    results := results.push r.toExerciseResult
  for (i, target, pts) in pinTargets do
    let r ← verifyDefViaComparator i target pts sheet
    results := results.push r.toExerciseResult

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    exitWithError <| "The autograder is unable to grade your submission "
        ++ "because no exercises have been marked as graded by your "
        ++ "instructor. Please notify your instructor of this error and "
        ++ "provide them with a link to this submission."
  return results

def testGradeSubmission (sheet submission : Environment)
    (sheetContents submissionContents : String) : IO (Array ExerciseResultDebug) := do
  writeComparatorRef sheetContents
  writeComparatorSolution submissionContents

  let mut defPinTargets : Array (Nat × PinTarget × Float × String) := #[]
  let mut results : Array ExerciseResultDebug := #[]
  let mut nextIdx := 0

  -- Proof candidates are handled separately below: Comparator looks up the
  -- challenge's theorem `name` by that same name in the solution, so testing
  -- multiple candidates against the same `name` can't share one
  -- `theorem name := candidate` alias in a single `Solution.lean` -- each needs
  -- its own rewrite-and-rebuild.
  let mut proofCandidates : Array (Name × Name × Float × String × String) := #[]

  for (name, constInfo) in sheet.constants.toList do
    if let some pts := autogradedProofAttr.getParam? sheet name then
      if not name.isInternal then
        for (subName, _) in submission.constants.toList do
          if let some (sheetName, expectedStatus) := autograderTestAttr.getParam? submission subName then
            if name == sheetName then
              let typeText ← renderType sheet constInfo.type
              proofCandidates := proofCandidates.push (name, subName, pts, expectedStatus, typeText)
    else if let some pts := autogradedDefAttr.getParam? sheet name then
      if not name.isInternal then
        for (subName, subConstInfo) in submission.constants.toList do
          if let some (sheetName, expectedStatus) := autograderTestAttr.getParam? submission subName then
            if name == sheetName then
              if let some failure := defQuickCheck subName name subConstInfo then
                results := results.push { failure with expected_status := expectedStatus }
              else
                let target : PinTarget :=
                  { subName, refName := name,
                    refTypeText := ← renderType sheet constInfo.type,
                    safetyKeyword := safetyKeywordFor constInfo }
                let i := nextIdx
                nextIdx := nextIdx + 1
                writeComparatorPin i target (combinedTacticBlock sheetContents (tacticsFor sheet name))
                defPinTargets := defPinTargets.push (i, target, pts, expectedStatus)

  for (i, target, pts, expectedStatus) in defPinTargets do
    let r ← verifyDefViaComparator i target pts sheet
    results := results.push { r with expected_status := expectedStatus }

  for (name, subName, pts, expectedStatus, typeText) in proofCandidates do
    writeComparatorSolution (submissionContents ++ s!"\ntheorem {name} : {typeText} := {subName}\n")
    let r ← verifyProofViaComparator name subName pts sheet
    results := results.push { r with expected_status := expectedStatus }

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    exitWithError <| "The autograder is unable to grade your submission "
        ++ "because no exercises have been marked as graded by your "
        ++ "instructor. Please notify your instructor of this error and "
        ++ "provide them with a link to this submission."

  return results

-- Returns a tuple of (fileName, outputMessage)
def moveFilesIntoPlace (localSubmission : Option String) : IO (String × String) := do
  match localSubmission with
  | none =>
    -- Copy the student's submission to the autograder directory. They should only
    -- have uploaded one Lean file; if they submitted more, we pick the first
    let submittedFiles ← submissionUploadDir.readDir
    let leanFiles := submittedFiles.filter
      (λ f => f.path.extension == some "lean")
    let some leanFile := leanFiles[0]?
      | exitWithError <| "Your submission was not graded because it did not "
          ++ "contain a Lean file. Make sure to upload a single .lean file "
          ++ "containing your solutions."
    IO.FS.writeFile submissionFileName (← IO.FS.readFile leanFile.path)
    let output :=
      if leanFiles.size > 1
      then "Warning: You submitted multiple Lean files. The autograder expects "
        ++ "you to submit a single Lean file containing your solutions, and it "
        ++ s!"will only grade a single file. It has picked {leanFile.fileName} "
        ++ "to grade; this may not be the file you intended to be graded.\n\n"
      else ""
    pure (leanFile.fileName, output)
  | some path =>
    IO.FS.writeFile submissionFileName (← IO.FS.readFile path)
    pure (path, "")

def moveTemplateIntoPlace (localTemplate : Option String) : IO Unit := do
  let assignmentPath ←
    match localTemplate with
    | none =>
      let configRaw ← IO.FS.readFile "config.json"
      let studentErrorText :=
        "The autograder failed to run because it is incorrectly configured. Please "
          ++ "notify your instructor of this error and provide them with a link to "
          ++ "your submission."
      let config ←
        try
          IO.ofExcept <| Json.parse configRaw
        catch _ =>
          exitWithError studentErrorText "Invalid JSON in autograder.json"
      if ← sheetFile.pathExists then FS.removeFile sheetFile
      IO.ofExcept <| config.getObjValAs? String "assignment_path"

    | some path => pure path
  IO.FS.writeFile sheetFile (← IO.FS.readFile assignmentPath)

def compileAutograder : IO Unit := do
  -- Compile the autograder so we get all our deps, even if the sheet itself
  -- fails to compile. Also ensures `comparator`/`lean4export` are built ahead of
  -- grading time.
  let compileArgs : Process.SpawnArgs := {
    cmd := "/root/.elan/bin/lake"
    args := #["build", "autograder", solutionDirName, "comparator", "lean4export"]
  }
  let out ← IO.Process.output compileArgs
  if out.exitCode != 0 then
    IO.println <| "WARNING: The autograder failed to compile. Note that this "
      ++ "may not be an error if your assignment template contains errors. "
      ++ "Compilation errors are printed below:\n"
      ++ out.stderr

def getErrorsStr (ml : MessageLog) : IO String := do
  let errorMsgs := ml.toList.filter (λ m => m.severity == .error)
  let errors ← errorMsgs.mapM (λ m => m.toString)
  let errorTxt := errors.foldl (λ acc e => acc ++ "\n" ++ e) ""
  return errorTxt

structure ConfigData where
  test            : Bool
  localRun        : Bool
  localSubmission : Option String
  localTemplate   : Option String
  deriving Repr

def parseArgsAux : ConfigData → List String → IO ConfigData
| cd, [] => pure cd
| cd, "--test"::rest => parseArgsAux { cd with test := true } rest
| cd, "--local"::submission::template::rest => parseArgsAux { cd with localRun := true, localSubmission := some submission, localTemplate := some template } rest
| _, s => exitWithError s!"Unknown argument: {s}"

def parseArgs : List String → IO ConfigData :=
  parseArgsAux ⟨false, false, none, none⟩

unsafe def main (args : List String) : IO Unit := do
  let cfg ← parseArgs args
  localRunRef.set cfg.localRun

  -- Get files into their appropriate locations
  let (studentFileName, output) ← moveFilesIntoPlace cfg.localSubmission
  moveTemplateIntoPlace cfg.localTemplate
  -- We need to compile the AutograderTests directory to ensure that any
  -- libraries on which we depend get compiled (even if the sheet itself fails
  -- to compile)

  if !cfg.localRun then compileAutograder

  -- Import the sheet (i.e., template/stencil)
  let sheetContents ← IO.FS.readFile sheetFile
  let sheetCtx := Parser.mkInputContext sheetContents sheetFileName
  let (sheetHeader, sheetParState, sheetMsgs) ← Parser.parseHeader sheetCtx

  enableInitializersExecution
  initSearchPath (← findSysroot)

  let (sheetHeadEnv, sheetMsgs)
    ← processHeader sheetHeader {} sheetMsgs sheetCtx

  if sheetMsgs.hasErrors then
    exitWithError (instructorInfo := (← getErrorsStr sheetMsgs)) <|
      "There was an error processing the assignment template's imports. This "
        ++ "error is unexpected. Please notify your instructor and provide a "
        ++ "link to your submission."

  let sheetCmdState : Command.State := Command.mkState sheetHeadEnv sheetMsgs {}
  let sheetFrontEndState
    ← IO.processCommands sheetCtx sheetParState sheetCmdState
  let sheet := sheetFrontEndState.commandState.env


  -- Grade the student submission
  -- Source: https://github.com/adamtopaz/lean_grader/blob/master/Main.lean
  let submissionContents ← IO.FS.readFile submissionFileName
  let inputCtx := Parser.mkInputContext submissionContents studentFileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  -- Enable initializers again before processing the submission's header: calling
  -- `processHeader` disables initializer execution as a side effect, and (unlike
  -- with older toolchains) it must be re-enabled before the second call.
  enableInitializersExecution
  let (headerEnv, messages) ← processHeader header {} messages inputCtx

  if messages.hasErrors then
    exitWithError <|
      "Your Lean file could not be processed because its header contains "
      ++ "errors. This is likely because you are attempting to import a module "
      ++ "that does not exist. A log of these errors is provided below; please "
      ++ "correct them and resubmit:\n\n"
      ++ (← getErrorsStr messages)

  let cmdState : Command.State := Command.mkState headerEnv messages {}
  let frontEndState ← IO.processCommands inputCtx parserState cmdState
  let messages := frontEndState.commandState.messages
  let submissionEnv := frontEndState.commandState.env

  let err ← getErrorsStr messages
  let output := output ++
    if messages.hasErrors
    then "Warning: Your submission contains one or more errors, which are "
          ++ "listed below. You should attempt to correct these errors prior "
          ++ "to your final submission. Any responses with errors will be "
          ++ "treated by the autograder as containing \"sorry.\"\n"
          ++ err
    else ""

  -- Provide debug info for staff
  IO.println "Submission compilation output:"
  let os ← messages.toList.mapM (λ m => m.toString)
  IO.println <| os.foldl (·++·) ""

  if cfg.test then
    let tests : Array ExerciseResultDebug ←
      testGradeSubmission sheet submissionEnv sheetContents submissionContents
    let mut map : Std.HashMap _ _ := ∅
    if cfg.localRun then
      println "Results:"
      -- Store exercise results in a map ⟨sheet_name, [results]⟩
      for er in tests do
        if let some ers := map[er.sheet_name]? then
          map := map.insert er.sheet_name (ers ++ [er])
        else
          map := map.insert er.sheet_name [er]
      -- Print results
      -- TODO: sort by name
      for (name, ers) in map.toList do
        IO.println s!"{name}"
        let mut correct := 0
        let mut total := 0
        for er in ers do
          er.print
          if er.status == er.expected_status then correct := correct + 1
          total := total + 1
        IO.println s!"Passed {correct}/{total} test cases!"
        IO.println ""
    else
      IO.FS.writeFile resultsJsonPath (toJson (tests.map fun exdbg => exdbg.toExerciseResult)).pretty
  else
    let tests : Array ExerciseResult ←
      gradeSubmission sheet submissionEnv sheetContents submissionContents
    let results : GradingResults := { tests, output }
    if cfg.localRun then results.print
    else IO.FS.writeFile resultsJsonPath (toJson results).pretty
