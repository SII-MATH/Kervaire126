module

public import KIP126.LinProgram.Generated.ModuleMaps.CetaToSphere
public import KIP126.LinProgram.Generated.ModuleMaps.CWToCeta
public import Lean.Elab.Command
public meta import Lean.Elab.Command

@[expose] public section


open KIP126.LinModule.RawData.Maps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod || (`KIP126.LinProgram.Model).isPrefixOf mod then
      throwError "native graph data imported mathematics or delivery: {mod}"
  for decl in [``CetaToSphere.rows, ``CetaToSphere.imageCode, ``CetaToSphere.imageCodes_size,
      ``CWToCeta.rows, ``CWToCeta.imageCode, ``CWToCeta.imageCodes_size] do
    for ax in (← collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "native graph data has an unexpected axiom: {decl}: {ax}"

example : CetaToSphere.sourceGeneratorCount = 887 := rfl
example : CWToCeta.sourceGeneratorCount = 844 := rfl
set_option maxRecDepth 16384 in
example : CetaToSphere.imageCode ⟨0, by decide⟩ = "" := by
  simp only [CetaToSphere.imageCode, CetaToSphere.imageCodes, Array.getElem_map]
  rfl
set_option maxRecDepth 16384 in
example : CWToCeta.imageCode ⟨0, by decide⟩ = "" := by
  simp only [CWToCeta.imageCode, CWToCeta.imageCodes, Array.getElem_map]
  rfl

set_option maxRecDepth 16384 in
example : (CetaToSphere.rows.toList.map ImageRow.id) = List.range 887 := by decide +kernel
set_option maxRecDepth 16384 in
example : (CWToCeta.rows.toList.map ImageRow.id) = List.range 844 := by decide +kernel
