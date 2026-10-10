import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Leibniz.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Internal.Leibniz.Proofs
import Lean.Elab.Command

/-! Generic geometric data and conditional internal Leibniz transport must
not depend on the fixed sphere foundation or any Lin/Milnor assumption. -/
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.Classical.Adams.SphereH6LongLayerMaps,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.squarePairing,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.leftPairing,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.rightPairing,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.Compatible,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.Compatible.square,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.Compatible.left,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.Compatible.right,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.RelativeBoundary,
      ``KIP126.Classical.Adams.SphereH6LongLayerMaps.internalD_square_eq_zero_of_cross_sum,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.internalD_of_relativeBoundary] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected geometric h6-pairing dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected geometric h6-pairing import: {m}"

#print axioms KIP126.Classical.Adams.AdamsLongLayerPairing.internalD_of_relativeBoundary
