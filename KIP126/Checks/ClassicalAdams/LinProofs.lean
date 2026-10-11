import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.LinProgram.Differentials
import Lean.Elab.Command

/-! This audit intentionally uses non-module imports so that Lean loads proof
bodies and private helpers throughout the dependency closure. Public module
imports alone omit those values and would leave the audit incomplete. -/



open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let expected := logical ++ [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation,
    ``KIP126.Computation.LinProofs.sphereTable_sound]
  for decl in [``KIP126.Computation.LinProofs.differential_of_lookup] do
    let axioms ← KIP126.Checks.AxiomInputs.checkStageConsumer expected decl
      "unexpected Lin proofs dependency"
    unless KIP126.Checks.AxiomInputs.uses axioms
        ``KIP126.Computation.LinProofs.sphereTable_sound do
      throwError "missing explicit Challenge 2 database trust boundary: {decl}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Main.Challenge).isPrefixOf m then
      throwError "unexpected Lin proofs import: {m}"

namespace KIP126.Checks
open Lean Elab Command

/-- Follow proof values, not package types: the same Challenge2 type still
contains its total computation fields, but these consumers must not read them. -/
def checkOneLineH6Consumer (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let forbidden := [`KIP126.Computation.LinProofs.sphereTable_sound,
    `KIP126.Computation.LinProofs.differential_of_lookup,
    `KIP126.Challenge2.ComputationInterface.results,
    `KIP126.Challenge2.ComputationResults.sphereTable_sound]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then
      throwError "fixed one-line consumer reads total computation results: {root}: {name}"
    let some info := env.find? name | continue
    -- Private helpers have `_private` names; use their defining module.
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => name
    unless (`KIP126).isPrefixOf owner do continue
    if let some value := info.value? (allowOpaque := true) then
      if (value.find? fun e => match e with
          | .proj n i _ =>
              (n == `KIP126.Challenge2.ComputationInterface && i == 1) ||
                n == `KIP126.Challenge2.ComputationResults
          | _ => false).isSome then
        throwError "fixed one-line consumer projects total computation results: {root}: {name}"
      pending := pending ++ value.getUsedConstants
  unless seen.contains `KIP126.Interface.Solution.LinProgram.row5541 &&
      seen.contains `KIP126.Main.StageInput.literature &&
      seen.contains `KIP126.Main.StageInput.computation do
    throwError "fixed one-line consumer lost its producer or same-witness inputs: {root}"
  let _ ← AxiomInputs.checkStageConsumer
    [``propext, ``Classical.choice, ``Quot.sound,
      ``KIP126.Classical.Adams.standardFoundation, `KIP126.Main.Axiom.challenge2]
    root "one-line consumer dependency audit"

end KIP126.Checks

run_cmd KIP126.Checks.checkOneLineH6Consumer ``KIP126.Computation.LinProofs.row5541

set_option maxRecDepth 2048 in
example : KIP126.Computation.LinProofs.RawData.lookup 86 0 = none := by rfl
set_option maxRecDepth 2048 in
example : KIP126.Computation.LinProofs.RawData.lookup 0 128 = none := by rfl

#print axioms KIP126.Computation.LinProofs.row5541
