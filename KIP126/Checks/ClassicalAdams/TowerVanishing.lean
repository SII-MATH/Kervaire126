module

public import KIP126.Def.ClassicalAdams.Detection.Vanishing
public import Lean.Elab.Command

@[expose] public section


open KIP126.Classical.Adams.TowerDetection
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod || (`KIP126.Def.StageInput).isPrefixOf mod then
      throwError "generic tower vanishing imports a fixed model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``filtration_raise_of_pageTwo_subsingleton,
      ``mem_all_filtrations_of_pageTwo_zero,
      ``homotopy_eq_zero_of_pageTwo_zero_of_separated] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected axiom {decl}: {ax}"

#print axioms filtration_raise_of_pageTwo_subsingleton
#print axioms mem_all_filtrations_of_pageTwo_zero
#print axioms homotopy_eq_zero_of_pageTwo_zero_of_separated
