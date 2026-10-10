import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Sphere.Proofs
import Lean.Elab.Command

/-! Audit the actual cooperation unit and the below-page unit/coaction
formula. Unit coherence is an explicit premise, not a new fixed axiom. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.Cohomology.cooperationUnit,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorUnit,
      ``KIP126.StableHomotopy.Cohomology.cooperationCounit_unit,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorUnit_apply,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorUnit_augmentation,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorUnit_injective,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorUnit_naturality,
      ``KIP126.StableHomotopy.Cohomology.Mod2KunnethUnitCompatible,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_unit,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarStep_unit_sub_coaction,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarStep_eq_zero_iff,
      ``KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_sphere,
      ``KIP126.StableHomotopy.Cohomology.mod2CobarStep_sphere_zero] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected Kunneth-unit dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerPages).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerDifferential).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerHomology).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.TowerResolution).isPrefixOf m ||
        (`KIP126.Def.Steenrod.MilnorCobar).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected below-page Kunneth-unit import: {m}"

#print axioms KIP126.StableHomotopy.Cohomology.cooperationTensorDiagonal_unit
#print axioms KIP126.StableHomotopy.Cohomology.mod2CobarStep_eq_zero_iff
#print axioms KIP126.StableHomotopy.Cohomology.mod2TensorCoaction_sphere
