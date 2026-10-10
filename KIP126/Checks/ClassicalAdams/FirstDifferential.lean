import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Image.Proofs
import Lean.Elab.Command

/-! Audit the derived comparison with the actual first quotient-page differential.
Ring structure, homology Künneth, tensor exactness, and unit/shift coherence
are explicit parameters, not newly postulated values for the fixed foundation. -/

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.connectingHomomorphism_naturality,
      ``KIP126.StableHomotopy.inducedMap_cast,
      ``KIP126.StableHomotopy.Cohomology.mod2UnitNatTrans,
      ``KIP126.StableHomotopy.Cohomology.mod2Unit_shift,
      ``KIP126.StableHomotopy.Cohomology.mod2FreeAction_outerUnit,
      ``KIP126.Classical.Adams.adamsResolutionSequence,
      ``KIP126.Classical.Adams.adamsHomologyD1,
      ``KIP126.Classical.Adams.adamsResolutionSequence_connecting,
      ``KIP126.Classical.Adams.adamsResolutionSequence_unit_last_square,
      ``KIP126.Classical.Adams.adamsResolutionDifferential_eq_homologyD1,
      ``KIP126.Classical.Adams.adamsPageD_one_homologyD1,
      ``KIP126.Classical.Adams.adamsHomologyAction_outerUnit,
      ``KIP126.Classical.Adams.adamsHomologyD1_eq_boundary_outerUnit,
      ``KIP126.Classical.Adams.adamsHomologyD1_tensor,
      ``KIP126.Classical.Adams.adamsPageD_one_tensor,
      ``KIP126.Classical.Adams.adamsHomologyD1_eq_cobarStep,
      ``KIP126.Classical.Adams.adamsPageD_one_cobarStep,
      ``KIP126.Classical.Adams.adamsHomologyD1_unit_sub_coaction,
      ``KIP126.Classical.Adams.adamsHomologyD1_eq_zero_iff,
      ``KIP126.Classical.Adams.adamsPageD_one_eq_zero_iff,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorComultiply_primitive,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensor_lof_cast,
      ``KIP126.StableHomotopy.Cohomology.cooperationCobarDiagonal,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorCobarSplit,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensor_unitParts,
      ``KIP126.StableHomotopy.Cohomology.cooperationTensorCobarSplit_lof_tmul,
      ``KIP126.Classical.Adams.adamsHomologyD1_tensorBoundary_cobar_recurrence,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_tensorBoundary_cobar,
      ``KIP126.Classical.Adams.adamsTensorBoundary_surjective,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_image_cobar_iff,
      ``KIP126.Classical.Adams.sphereAdamsPageD_one_128_image_cobar_iff,
      ``KIP126.Classical.Adams.adamsHomologyD1_tensorBoundary_primitive,
      ``KIP126.Classical.Adams.sphereAdamsHomologyD1_tensorBoundary_primitive,
      ``KIP126.Classical.Adams.sphereAdamsPageD_one_tensorBoundary_primitive] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected first-differential dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.Steenrod.MilnorCobar).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected first-differential import: {m}"

#print axioms KIP126.Classical.Adams.adamsHomologyD1_eq_boundary_outerUnit
#print axioms KIP126.Classical.Adams.adamsPageD_one_cobarStep
#print axioms KIP126.Classical.Adams.adamsPageD_one_eq_zero_iff
#print axioms KIP126.Classical.Adams.sphereAdamsPageD_one_tensorBoundary_primitive
#print axioms KIP126.Classical.Adams.sphereAdamsPageD_one_128_image_cobar_iff
