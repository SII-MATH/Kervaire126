import KIP126.Def.ClassicalAdams.UnitFiber.Connectivity.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Right.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Boundary.Right.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Representatives.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Cycles.Proofs
import Lean.Elab.Command

/-! Audit the map-preserving smash comparison independently of all fixed
foundation, Milnor, Lin, and spectral-sequence adapter assumptions. -/

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.adamsTensorFiberTriangleIso,
      ``KIP126.Classical.Adams.adamsFiberTensorIso,
      ``KIP126.Classical.Adams.adamsTensorFiberTriangleIso_hom₂,
      ``KIP126.Classical.Adams.adamsTensorFiberTriangleIso_hom₃,
      ``KIP126.Classical.Adams.adamsFiberTensorIso_inv_δ,
      ``KIP126.Classical.Adams.adamsFiberTensorIso_inv_ι,
      ``KIP126.Classical.Adams.adamsFiberTensorIso_hom_ι,
      ``KIP126.Classical.Adams.adamsSmashTower,
      ``KIP126.Classical.Adams.adamsSmashTowerStep,
      ``KIP126.Classical.Adams.adamsSmashTowerComposite,
      ``KIP126.Classical.Adams.adamsTowerSmashIso,
      ``KIP126.Classical.Adams.adamsTowerSmashIso_step,
      ``KIP126.Classical.Adams.adamsTowerSmashIso_composite,
      ``KIP126.Classical.Adams.adamsTowerSmashIso_lift_iff,
      ``KIP126.Classical.Adams.adamsSmashSphereTensorIso,
      ``KIP126.Classical.Adams.adamsSmashTowerNestingIso,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingIso,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingIso_zero,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingIso_succ,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingIso_step_left,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_comparison,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_left,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingNextRight,
      ``KIP126.Classical.Adams.UnitFiberInclusionCommutes,
      ``KIP126.Classical.Adams.unitFiberInclusionCommutes_tensor,
      ``KIP126.Classical.Adams.adamsSmashTowerStep_succ_of_inclusion_commutes,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingNextRight_zero,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingNextRight_succ,
      ``KIP126.Classical.Adams.adamsSmashSpherePairingIso_step_right,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingNextRight,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingNextRight_comparison,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_right,
      ``KIP126.Classical.Adams.fiberι_postcomp_injective_of_vanishing,
      ``KIP126.Classical.Adams.unitFiberInclusion_postcomp_eq,
      ``KIP126.Classical.Adams.unitFiberInclusionCommutes_of_vanishing,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_right_of_vanishing,
      ``KIP126.Classical.Adams.unitFiber_mapping_vanishing_of_tStructure,
      ``KIP126.Classical.Adams.unitFiberInclusionCommutes_of_tStructure,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_right_of_tStructure,
      ``KIP126.Classical.Adams.fiberι_homotopy_injective_of_surjective,
      ``KIP126.Classical.Adams.mod2Unit_homotopy_surjective,
      ``KIP126.Classical.Adams.mod2UnitFiber_homotopy_injective,
      ``KIP126.Classical.Adams.mod2UnitFiber_homotopy_subsingleton,
      ``KIP126.Classical.Adams.mod2UnitFiber_isLE_of_homotopy,
      ``KIP126.Classical.Adams.mod2EilenbergMacLane_isGE_of_homotopy,
      ``KIP126.Classical.Adams.mod2UnitFiber_inclusionCommutes_of_homotopy,
      ``KIP126.Classical.Adams.mod2SpherePairing_step_right_of_homotopy,
      ``KIP126.Classical.Adams.adamsSphereLayerPairingTriangleIso,
      ``KIP126.Classical.Adams.adamsSphereLayerPairingIso,
      ``KIP126.Classical.Adams.adamsSphereLayerPairingTriangleIso_hom₁,
      ``KIP126.Classical.Adams.adamsSphereLayerPairingTriangleIso_hom₂,
      ``KIP126.Classical.Adams.adamsSphereLayerPairingIso_ι,
      ``KIP126.Classical.Adams.adamsSphereLayerPairingIso_δ,
      ``KIP126.Classical.Adams.adamsSphereTowerLayerPairingTriangleIso,
      ``KIP126.Classical.Adams.adamsSphereTowerLayerPairingIso,
      ``KIP126.Classical.Adams.adamsSphereTowerLayerPairingTriangleIso_hom₁,
      ``KIP126.Classical.Adams.adamsSphereTowerLayerPairingTriangleIso_hom₂,
      ``KIP126.Classical.Adams.adamsSphereTowerLayerPairingIso_ι,
      ``KIP126.Classical.Adams.adamsSphereTowerLayerPairingIso_δ,
      ``KIP126.Classical.Adams.adamsSphereMixedLayerPairings_agree,
      ``KIP126.StableHomotopy.Cohomology.mod2CoefficientPairing,
      ``KIP126.StableHomotopy.Cohomology.mod2Unit_tensor_mul,
      ``KIP126.StableHomotopy.Cohomology.mod2CoefficientPairing_unit,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_comparison,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι,
      ``KIP126.StableHomotopy.Cohomology.mod2CoefficientPairing_unit_right,
      ``KIP126.StableHomotopy.Cohomology.mod2CoefficientPairing_unit_left,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_right_comparison,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_comparison,
      ``KIP126.StableHomotopy.RightTensorSuspensionCompatibility,
      ``KIP126.StableHomotopy.rightTensorSuspension_pairing,
      ``KIP126.Classical.Adams.adamsFiberTensorIso_pairing_δ,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_succ_comparison,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_δ_left,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_right_δ_comparison,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_right_δ,
      ``KIP126.StableHomotopy.TensorSuspensionBraidingCompatibility,
      ``KIP126.StableHomotopy.braidedTensorPairing_swap,
      ``KIP126.StableHomotopy.braidedSuspension_transport,
      ``KIP126.Classical.Adams.adamsFiberTensorPairingRight,
      ``KIP126.Classical.Adams.adamsFiberTensorPairingRight_δ,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingBoundaryRight,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingBoundaryRight_δ,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingBoundaryRight_obstruction,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ_comparison,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ_ordered_iff,
      ``KIP126.Classical.Adams.adamsK_eq_zero_iff_comp_δ_eq_zero,
      ``KIP126.Classical.Adams.adamsCycles_mem_of_comp_δ_eq_zero,
      ``KIP126.Classical.Adams.adamsCycleSubmodule_top_mem_of_comp_δ_eq_zero,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_comp_δ_eq_zero,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_mem_cycles,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ_representatives,
      ``KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ_representatives_ordered_iff] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless logical.contains a do
        throwError "unexpected tower-smash dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected tower-smash import: {m}"

#print axioms KIP126.Classical.Adams.adamsFiberTensorIso_hom_ι
#print axioms KIP126.Classical.Adams.adamsFiberTensorIso_inv_δ
#print axioms KIP126.Classical.Adams.adamsTowerSmashIso_composite
#print axioms KIP126.Classical.Adams.adamsTowerSmashIso_lift_iff
#print axioms KIP126.Classical.Adams.adamsSmashSpherePairingIso_step_left
#print axioms KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_left
#print axioms KIP126.Classical.Adams.adamsSmashSpherePairingIso_step_right
#print axioms KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_right
#print axioms KIP126.Classical.Adams.fiberι_postcomp_injective_of_vanishing
#print axioms KIP126.Classical.Adams.unitFiberInclusionCommutes_of_vanishing
#print axioms KIP126.Classical.Adams.adamsTowerSpherePairingIso_step_right_of_tStructure
#print axioms KIP126.Classical.Adams.mod2UnitFiber_homotopy_injective
#print axioms KIP126.Classical.Adams.mod2SpherePairing_step_right_of_homotopy
#print axioms KIP126.Classical.Adams.adamsSphereLayerPairingIso_δ
#print axioms KIP126.Classical.Adams.adamsSphereTowerLayerPairingIso_δ
#print axioms KIP126.Classical.Adams.adamsSphereMixedLayerPairings_agree
#print axioms KIP126.StableHomotopy.Cohomology.mod2CoefficientPairing_unit
#print axioms KIP126.Classical.Adams.adamsSphereLayerProduct_ι
#print axioms KIP126.Classical.Adams.adamsSphereLayerProduct_ι_right_comparison
#print axioms KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_comparison
#print axioms KIP126.Classical.Adams.adamsTowerSpherePairingIso_δ_left
#print axioms KIP126.Classical.Adams.adamsSphereLayerProduct_ι_right_δ
#print axioms KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ
#print axioms KIP126.Classical.Adams.adamsSphereLayerProduct_ι_left_δ_ordered_iff
