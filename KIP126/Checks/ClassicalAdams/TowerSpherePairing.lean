import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.One.Page.Proofs
import Lean.Elab.Command

/-! Audit the specified coefficient product and the constructed one-step
pairing. This does not certify higher-page pairings or a concrete model. -/
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``KIP126.StableHomotopy.sphereTensorIsoFromRightShift,
      ``KIP126.StableHomotopy.tensorHomPairing,
      ``KIP126.StableHomotopy.homotopyTensorPairing,
      ``KIP126.StableHomotopy.tensorHomPairing_apply,
      ``KIP126.StableHomotopy.tensorHomPairing_naturality,
      ``KIP126.StableHomotopy.homotopyTensorPairing_naturality,
      ``KIP126.StableHomotopy.cofiberFactorizationMap_isIso,
      ``KIP126.Classical.Adams.adamsLongLayerProjection_one_isIso,
      ``KIP126.Classical.Adams.adamsSphereLayerProductOrdered,
      ``KIP126.Classical.Adams.adamsSphereE1Product,
      ``KIP126.Classical.Adams.adamsSphereLongLayerPairing,
      ``KIP126.Classical.Adams.adamsSphereLongLayerPairing_projection,
      ``KIP126.Classical.Adams.adamsSphereLongLayerOneProduct,
      ``KIP126.Classical.Adams.adamsSphereLongLayerOnePairing,
      ``KIP126.Classical.Adams.AdamsLongLayerPairing.boundaryCompatible_one,
      ``KIP126.Classical.Adams.adamsSphereLongLayerOneProduct_projection,
      ``KIP126.Classical.Adams.adamsSphereLongLayerOnePairing_projection,
      ``KIP126.Classical.Adams.adamsSpherePageOneProduct,
      ``KIP126.Classical.Adams.adamsSpherePageOneProduct_long] do
    for a in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains a do
        throwError "unexpected sphere-pairing dependency: {declaration}: {a}"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m ||
        (`KIP126.Def.StageInput).isPrefixOf m ||
        (`KIP126.Def.ClassicalAdams.MilnorCooperations).isPrefixOf m ||
        (`KIP126.Def.AdamsE2).isPrefixOf m then
      throwError "unexpected sphere-pairing import: {m}"

#print axioms KIP126.Classical.Adams.adamsSpherePageOneProduct_long
#print axioms KIP126.Classical.Adams.adamsSphereLongLayerPairing_projection
