module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Proofs
public import KIP126.Def.ClassicalAdams.Detection.Filtered.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! The constructed one-sided long-layer pairing lives on actual tower and
cofiber objects. This audit forbids producer/consumer imports and checks every
construction and formula independently of the fixed model's admitted fields. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic long-layer construction imported a project delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Classical.Adams.TowerDetection.Detects.exists_towerLift,
      ``KIP126.Classical.Adams.adamsTowerSpherePairingIso_map_left,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStagePairingIso,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_hom₁,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_hom₂,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_ι,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_δ,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_connecting,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_connecting_eq_zero,
      ``KIP126.Classical.Adams.adamsSphereLongLayerStagePairingIso_connecting_eq_zero,
      ``KIP126.Classical.Adams.adamsDifferential_longLayerStagePairing_eq_zero] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in geometric long-layer construction {decl}: {ax}"

#print axioms KIP126.Classical.Adams.adamsSphereLongLayerStagePairingIso
#print axioms KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_δ
#print axioms KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_connecting

#print axioms KIP126.Classical.Adams.TowerDetection.Detects.exists_towerLift

#print axioms KIP126.Classical.Adams.adamsSphereLongLayerStageTriangleIso_connecting_eq_zero
#print axioms KIP126.Classical.Adams.adamsSphereLongLayerStagePairingIso_connecting_eq_zero
#print axioms KIP126.Classical.Adams.adamsDifferential_longLayerStagePairing_eq_zero
