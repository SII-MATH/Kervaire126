module

public import KIP126.Checks.AxiomInputs
public import KIP126.Mathlib.ClassicalAdams.FinalComparison.Proofs
public import Lean.Elab.Command
public meta import KIP126.Checks.AxiomInputs
import all KIP126.Mathlib.ClassicalAdams.FinalComparison.Proofs

@[expose] public section

/-! Guard the theorem form and the three disclosed fixed inputs. Development
checks report inherited Challenge2 type debt; strict proof completion remains
an explicit `kip126.checks.strictStageConsumerAudit` obligation. -/

open Lean Elab Command in
run_cmd do
  let declaration := ``KIP126.Classical.Adams.h6Square_comparison
  let some (.thmInfo _) := (← getEnv).find? declaration
    | throwError "the specified-class comparison must be a theorem, not an axiom"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let inputs := [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.standardMilnorCooperations,
    ``KIP126.Classical.Adams.linE2Presentation]
  discard <| KIP126.Checks.AxiomInputs.checkStageConsumer (logical ++ inputs)
    declaration "unexpected specified-class comparison dependency"

#print axioms KIP126.Classical.Adams.h6Square_comparison
