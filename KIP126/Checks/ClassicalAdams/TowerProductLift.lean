import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Differential.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Lifting.Construction.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Boundary.FirstDifferential.Proofs
import Lean.Elab.Command

/-! Audit construction from connecting lifts and its actual differential
formula. No fixed sphere, Lin or Milnor assumption belongs in this layer. -/
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.cofiberFactorizationMap_lift_of_boundary,
      ``KIP126.StableHomotopy.cofiberFactorizationMap_lift_iff,
      ``KIP126.StableHomotopy.connectingHomomorphism_eq_desuspend,
      ``KIP126.Classical.Adams.adamsLongLayerProjection_lift_of_boundary,
      ``KIP126.Classical.Adams.adamsLongLayerProjection_lift_iff,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProjectedProduct,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProductBoundary,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProduct_exists_of_boundaryLift,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProduct_exists_iff_boundaryLift,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProductOfBoundaryLift,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProductOfBoundaryLift_projection,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProductOfBoundaryLift_boundary,
      ``KIP126.Classical.Adams.adamsSphereLongLayerPairingOfBoundaryLift_projection,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProductOfBoundaryLift_K,
      ``KIP126.Classical.Adams.adamsSphereLongLayerProductOfBoundaryLift_differential,
      ``KIP126.Classical.Adams.SphereH6BoundaryLifts,
      ``KIP126.Classical.Adams.SphereH6BoundaryLifts.FitsProducts,
      ``KIP126.Classical.Adams.SphereH6BoundaryLifts.toLongLayerMaps,
      ``KIP126.Classical.Adams.SphereH6BoundaryLifts.toLongLayerMaps_boundaries,
      ``KIP126.Classical.Adams.SphereH6BoundaryLifts.toLongLayerMaps_compatible,
      ``KIP126.Classical.Adams.adamsBoundaries_succ_eq_of_differential_zero,
      ``KIP126.Classical.Adams.sphereAdamsBoundaries_filtration_one_succ,
      ``KIP126.Classical.Adams.sphereAdamsBoundaries_filtration_one,
      ``KIP126.Classical.Adams.adamsJ_eq_zero_of_boundaries_eq_bot,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.boundaryCompatible_of_eq_bot,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.CrossBoundaryCompatible,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.square_boundary,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.CrossBoundaryCompatible.left_boundary,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.CrossBoundaryCompatible.right_boundary,
      ``KIP126.Classical.Adams.SphereH6BoundaryLifts.toLongLayerMaps_compatible_of_cross,
      ``KIP126.Classical.Adams.adamsPageOneEquiv_d_mem_boundaries,
      ``KIP126.Classical.Adams.adamsBoundary_two_exists_first_primitive,
      ``KIP126.Classical.Adams.SphereH6FirstCycleProductRule,
      ``KIP126.Classical.Adams.SphereH6FirstCycleProductRule.crossBoundaryCompatible] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected product-lift dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected product-lift import: {m}"

#print axioms KIP126.Classical.Adams.adamsSphereLongLayerProductOfBoundaryLift_differential
#print axioms KIP126.Classical.Adams.SphereH6BoundaryLifts.toLongLayerMaps_compatible
#print axioms KIP126.Classical.Adams.SphereH6BoundaryLifts.toLongLayerMaps_compatible_of_cross
#print axioms KIP126.Classical.Adams.SphereH6FirstCycleProductRule.crossBoundaryCompatible
