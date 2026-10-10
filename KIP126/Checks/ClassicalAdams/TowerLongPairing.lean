import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Internal.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Leibniz.Proofs
import Lean.Elab.Command

/-! This audits conditional quotient descent, not the existence of geometric
pairing witnesses, their signs, or their compatibility with Lin multiplication. -/
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.AdamsLongLayerPairing,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.ProjectionCompatible,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.BoundaryCompatible,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.mem_cycles,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.boundary_left,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.boundary_right,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onCycles,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.cyclesToPage,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.boundaries_le_left_ker,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.boundaries_le_right_ker,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onPage,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onPage_mk,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onPage_long,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onPage_unique,
      ``KIP126.Classical.Adams.adamsLongLayerBoundaryToPage,
      ``KIP126.Classical.Adams.adamsDifferential_longLayerToPage_eq_boundary,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.RelativeBoundaryFormula,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.leibniz_of_relativeBoundary,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.relativeBoundary_iff_leibniz,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onInternalPage,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onInternalPage_comparison,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.onInternalPage_long] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected long-pairing dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected long-pairing import: {m}"

#print axioms KIP126.Classical.Adams.AdamsLongLayerPairing.onPage
#print axioms KIP126.Classical.Adams.AdamsLongLayerPairing.relativeBoundary_iff_leibniz
#print axioms KIP126.Classical.Adams.AdamsLongLayerPairing.onInternalPage_long
