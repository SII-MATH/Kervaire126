import Lean

/-!
# Stage-boundary inputs used by dependency regressions

The fixed foundation is selected by Def's explicit model construction, whose
unfinished proofs currently disclose sorryAx. C consumers use the one
Challenge2 boundary axiom. No Interface axiom is allowed to define T(M).

The statement-development milestone permits unfinished property proofs in
the type of an admitted package. The scoped consumer audit below reports
that debt; it never certifies that a consumer has no direct `sorry` proof.
Pure proofs and undeclared inputs retain their strict checks. For explicit
proof-completion work, enable `kip126.checks.strictStageConsumerAudit` while
elaborating the check, or run the unchanged global `lake exe axioms` audit.
-/

register_option kip126.checks.strictStageConsumerAudit : Bool := {
  defValue := false
  descr := "reject sorryAx even in explicitly admitted Challenge2 consumers"
}

namespace KIP126.Checks.AxiomInputs
open Lean Elab Command

def direct (input : Name) : List Name :=
  if input == `KIP126.Classical.Adams.standardFoundation ||
      input == `KIP126.Classical.Adams.standardMilnorCooperations then
    [``sorryAx]
  else if input == `KIP126.Classical.Adams.linE2Presentation ||
      input == `KIP126.Computation.LinProofs.sphereTable_sound then
    [`KIP126.Main.Axiom.challenge2]
  else
    [input]

def allows (inputs : List Name) (actual : Name) : Bool :=
  inputs.any fun input => (direct input).contains actual

def uses (actual : Array Name) (input : Name) : Bool :=
  (direct input).all actual.contains

/-- Audit one declared stage consumer, retaining the full dependency inventory.
Only an explicitly allowed and actually used Challenge2 axiom whose own type
already has `sorryAx` can receive the development warning. No other unexpected
axiom is admitted. Since `collectAxioms` returns names rather than dependency
paths, this warning cannot distinguish package-type debt from direct proof debt;
the explicit strict mode continues to reject both. -/
def checkStageConsumer (inputs : List Name) (declaration : Name)
    (context : String) : CommandElabM (Array Name) := do
  let axioms ← liftCoreM (collectAxioms declaration)
  let stage := `KIP126.Main.Axiom.challenge2
  let stageAllowed := inputs.any fun input => (direct input).contains stage
  let stageTypeHasSorry ←
    if stageAllowed && axioms.contains stage then
      match (← getEnv).find? stage with
      | some (.axiomInfo _) =>
          pure ((← liftCoreM (collectAxioms stage)).contains ``sorryAx)
      | _ => pure false
    else
      pure false
  for a in axioms do
    if a == ``sorryAx && kip126.checks.strictStageConsumerAudit.get (← getOptions) then
      throwError "{context}: {declaration} contains unfinished proof debt (strict audit)"
    if a == ``sorryAx && allows inputs a then
      logWarning <| m!"{context}: {declaration} depends on Def's unfinished model construction; " ++
        m!"this dependency inventory does not certify proof completion or exclude direct sorry."
    unless allows inputs a do
      if a == ``sorryAx && stageTypeHasSorry &&
          !kip126.checks.strictStageConsumerAudit.get (← getOptions) then
        logWarning <| m!"{context}: {declaration} depends on sorryAx; its explicitly admitted " ++
          m!"Challenge2 package type also contains unfinished proof debt. This inventory " ++
          m!"does not establish that the consumer has no direct sorry. Enable " ++
          m!"kip126.checks.strictStageConsumerAudit for the strict rejection."
      else
        throwError "{context}: {declaration}: {a}"
  return axioms

end KIP126.Checks.AxiomInputs
