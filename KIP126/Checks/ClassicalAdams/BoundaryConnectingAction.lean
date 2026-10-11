module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.BoundaryTower.Connecting.Proofs
public import Lean.Elab.Command

@[expose] public section


open KIP126.Classical.Adams.BoundaryConnectingAction
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod || (`KIP126.Def.StageInput).isPrefixOf mod then
      throwError "generic connecting action imports a model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``longK_range, ``projectedLongK_range,
      ``existsUnique_boundary_action, ``boundary_mul_same_projected_longK] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected connecting action axiom {decl}: {ax}"

#print axioms existsUnique_boundary_action
