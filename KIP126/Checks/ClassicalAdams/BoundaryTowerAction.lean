module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.BoundaryTower.Proofs
public import Lean.Elab.Command

@[expose] public section


open KIP126.Classical.Adams.BoundaryTowerAction
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod || (`KIP126.Def.StageInput).isPrefixOf mod then
      throwError "generic boundary action imports an actual model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``tower_kernel_left, ``tower_boundary_kernel_left,
      ``coefficient_mem_boundaries, ``e1Product_mem_boundaries,
      ``boundary_mul_kerK, ``boundary_mul_longLayer_zeroK,
      ``boundary_mul_sameK] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected boundary action axiom {decl}: {ax}"

#print axioms KIP126.Classical.Adams.BoundaryTowerAction.boundary_mul_sameK
