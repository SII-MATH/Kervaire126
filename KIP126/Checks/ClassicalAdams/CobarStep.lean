import KIP126.Def.StableHomotopy.Cohomology.Cooperations.CobarStep.Reduced.Proofs
import Lean.Elab.Command

/-! The reduced step is constructed before the Adams differential comparison.
In particular, its definition cannot simply rename the actual page differential. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.Cohomology.mod2OuterUnitMap,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarDifference,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarDifference_apply,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarDifference_augmentation,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarStep,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarStep_inclusion,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationTensorInclusion_injective] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected reduced-step dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerHomology).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerResolution).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerDifferential).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerPages).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected reduced-step import: {m}"

#print axioms KIP126.StableHomotopy.Cohomology.mod2CobarStep
#print axioms KIP126.StableHomotopy.Cohomology.mod2CobarStep_inclusion
