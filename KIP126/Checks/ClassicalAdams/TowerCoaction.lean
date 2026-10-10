import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Boundary.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Nonvanishing.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Coordinates.Proofs
import Lean.Elab.Command

/-! Audit the actual next-stage coaction formula. It is a consequence of
general homology coherence and the already constructed normalized boundary. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsHomologyBoundary_eq_connecting,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorAugmentation_lof_tmul_eq_zero,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensor_lof_tmul_ne_zero,
      ``KIP126.Classical.Adams.adamsTensorBoundary_eq_zero_iff_of_augmentation_eq_zero,
      ``KIP126.Classical.Adams.adamsTensorBoundary_lof_tmul_ne_zero,
      ``KIP126.Classical.Adams.sphereAdamsPageOne_tensorBoundary_ne_zero,
      ``KIP126.Classical.Adams.adamsTensorCoaction_boundary,
      ``KIP126.Classical.Adams.adamsTensorCoaction_next,
      ``KIP126.Classical.Adams.adamsTensorBoundary,
      ``KIP126.Classical.Adams.adamsTensorBoundary_comparison,
      ``KIP126.Classical.Adams.adamsNextHomologyTensorEquiv_normalized,
      ``KIP126.Classical.Adams.adamsTensorBoundary_normalization,
      ``KIP126.StableHomotopy.Cohomology.reducedCooperationTensorInclusion_lof_tmul,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorAugmentation_reduced_inclusion,
      ``KIP126.Classical.Adams.adamsNextHomologyTensorEquiv_boundary_reduced,
      ``KIP126.Classical.Adams.adamsNextHomologyTensorEquiv_boundary_lof_tmul,
      ``KIP126.Classical.Adams.adamsTensorBoundary_surjective,
      ``KIP126.Classical.Adams.adamsTensorCoaction_next_coproduct,
      ``KIP126.Classical.Adams.adamsTensorCoaction_tensorBoundary,
      ``KIP126.Classical.Adams.adamsTensorBoundary_unit,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorLowerMap_unit] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected tower-coaction dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.Steenrod.MilnorCobar).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected tower-coaction import: {m}"

#print axioms KIP126.Classical.Adams.adamsTensorCoaction_boundary
#print axioms KIP126.Classical.Adams.adamsTensorCoaction_next
#print axioms KIP126.Classical.Adams.adamsTensorCoaction_next_coproduct
#print axioms KIP126.Classical.Adams.adamsTensorCoaction_tensorBoundary
