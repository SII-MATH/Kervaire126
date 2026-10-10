import KIP126.Def.ClassicalAdams.TowerLongLayer.Internal.Proofs
import Lean.Elab.Command

/-! Audit all-page long-cofiber representatives without fixed foundations,
Milnor/Lin assumptions, tensor compatibility, or spectral-sequence adapters. -/
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.cofiberFactorizationMap,
      ``KIP126.StableHomotopy.cofiberFactorizationMap_ι,
      ``KIP126.StableHomotopy.cofiberFactorizationMap_δ,
      ``KIP126.StableHomotopy.cofiberFactorizationMap_connecting,
      ``KIP126.StableHomotopy.cofiberFactorizationMap_image_iff,
      ``KIP126.Classical.Adams.adamsLongLayer,
      ``KIP126.Classical.Adams.adamsLongLayerProjection,
      ``KIP126.Classical.Adams.adamsLongLayerToE1,
      ``KIP126.Classical.Adams.adamsLongLayerK,
      ``KIP126.Classical.Adams.adamsLongLayerK_lift,
      ``KIP126.Classical.Adams.adamsCycles_mem_iff_longLayer,
      ``KIP126.Classical.Adams.adamsLongLayerToE1_mem_cycles,
      ``KIP126.Classical.Adams.adamsCycles_eq_range_longLayer,
      ``KIP126.Classical.Adams.adamsDifferential_of_longLayer,
      ``KIP126.Classical.Adams.adamsLongLayerToCycles,
      ``KIP126.Classical.Adams.adamsLongLayerToPage,
      ``KIP126.Classical.Adams.adamsLongLayerToCycles_surjective,
      ``KIP126.Classical.Adams.adamsLongLayerToPage_surjective,
      ``KIP126.Classical.Adams.adamsDifferential_longLayerToPage,
      ``KIP126.Classical.Adams.adamsLongLayerToInternalPage,
      ``KIP126.Classical.Adams.adamsLongLayerToInternalPage_comparison,
      ``KIP126.Classical.Adams.adamsLongLayerToInternalPage_surjective,
      ``KIP126.Classical.Adams.adamsTowerInternalD_longLayer] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected long-layer dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected long-layer import: {m}"

#print axioms KIP126.Classical.Adams.adamsCycles_eq_range_longLayer
#print axioms KIP126.Classical.Adams.adamsLongLayerToPage_surjective
#print axioms KIP126.Classical.Adams.adamsDifferential_longLayerToPage
#print axioms KIP126.Classical.Adams.adamsTowerInternalD_longLayer
