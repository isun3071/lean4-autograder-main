import Lean

open Lean Lean.Elab.Tactic

-- Main autograder attributes
declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := autograded_proof) "autogradedProof" ptVal : attr
syntax (name := autograded_def) "autogradedDef" ptVal : attr

initialize autogradedProofAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `autograded_proof
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autogradedProof $pts:num) => return pts.getNat.toFloat
      | `(attr| autogradedProof $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid autograded proof attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize autogradedDefAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `autograded_def
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autogradedDef $pts:num) => return pts.getNat.toFloat
      | `(attr| autogradedDef $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid autograded definition attribute"
    afterSet := λ _ _ => do pure ()
  }

-- Customize valid axioms
syntax:50 (name := valid_axioms) "validAxioms" "#[" sepBy(ident, ",") "]" : attr

initialize validAxiomsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `valid_axioms
    descr := "Specifies the axioms allowed in a proof"
    getParam := λ _ stx =>
      match stx with
        | `(attr| validAxioms #[$axs,*]) =>
          return axs.getElems.map fun ax => (
          ax.raw.prettyPrint.pretty.toName)
        | _ => throwError "Invalid valid axiom attribute"
    afterSet := λ _ _ => do pure ()
  }


-- Autograder tactics attributes
syntax:50 (name := valid_tactics) "validTactics" "#[" sepBy(tactic, ",") "]" : attr
syntax:50 (name := default_tactics) "defaultTactics" "#[" sepBy(tactic, ",") "]" : attr

initialize validTacticsAttr : ParametricAttribute (Array (String × Syntax)) ←
  registerParametricAttribute {
    name := `valid_tactics
    descr := "Specifies the tactics run to validate a solution"
    getParam := λ _ stx =>
      match stx with
        | `(attr| validTactics #[$tacs,*]) =>
          return tacs.getElems.map fun tac => (
            tac.prettyPrint.pretty.trimAscii.copy,
            tac)
        | _ => throwError "Invalid valid tactic attribute"
    afterSet := λ _ _ => do pure ()
  }


-- We expect this to be an attribute that is set up over the config definition
initialize defaultTacticsAttr : ParametricAttribute (Array (String × Syntax)) ←
  registerParametricAttribute {
    name := `default_tactics
    descr := "Specifies the default tactics run to validate a solution"
    getParam := λ _ stx =>
      match stx with
        | `(attr| defaultTactics #[$tacs,*]) =>
          return tacs.getElems.map fun tac => (
            tac.prettyPrint.pretty.trimAscii.copy,
            tac)
        | _ => throwError "Invalid default tactic attribute"
    afterSet := λ _ _ => do pure ()
  }

-- Testing the autograder
declare_syntax_cat exerciseType
syntax "proof" : exerciseType
syntax "def" : exerciseType

declare_syntax_cat status
syntax "passes" : status
syntax "fails" : status

syntax (name := autograder_test) "autograderTest" status name : attr

initialize autograderTestAttr : ParametricAttribute (Name × String) ←
  registerParametricAttribute {
    name := `autograder_test
    descr := "For testing purposes, specifies whether a submission is expected to pass or fail a test"
    getParam := λ _ stx => match stx with
      | `(attr| autograderTest passes $n) => return (n.getName, "passed")
      | `(attr| autograderTest fails $n) => return (n.getName, "failed")
      | _ => throwError "Invalid test autograder attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize legalAxiomAttr : TagAttribute ←
  registerTagAttribute `legalAxiom
    "Marks an axiom as acceptable for use in autograded solutions"

/-! ## Restricting which tactics a student may use

`@[autogradedProof]` only ever checks that a submitted proof *closes the stated
theorem* using permitted axioms; it says nothing about how the student got there.
That leaves a gap whenever an assignment asks students to practice a particular
technique: a one-word `grind` or `simp` closes many such exercises outright and
would otherwise be awarded full credit.

`@[allowedTactics #["rewrite", "rfl"]]` closes that gap by naming the *only*
tactics permitted in a given proof. It is an allowlist, not a blocklist, so a
tactic nobody thought to forbid is rejected by default rather than accepted.

Tactics are named by the keyword a student actually types (`"rewrite"`, `"rfl"`,
`"intro"`). String literals are used rather than identifiers so that tactics whose
names are not valid Lean identifiers -- `"exact?"`, `"<;>"` -- can be named too. -/
syntax:50 (name := allowed_tactics) "allowedTactics" "#[" sepBy(str, ",") "]" : attr

initialize allowedTacticsAttr : ParametricAttribute (Array String) ←
  registerParametricAttribute {
    name := `allowed_tactics
    descr := "Specifies the only tactics permitted in a student's proof"
    getParam := λ _ stx =>
      match stx with
        | `(attr| allowedTactics #[$tacs,*]) =>
          return tacs.getElems.map (fun s => s.getString)
        | _ => throwError "Invalid allowedTactics attribute"
    afterSet := λ _ _ => do pure ()
  }
