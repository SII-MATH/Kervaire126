module

public import KIP126.LinProgram.Certificates.StemFour
public import Lean.Elab.Command

@[expose] public section


namespace KIP126.LinE2.StemFour

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "whole component vanishing imports a delivery or basis assumption: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``generator_internal_le_seven, ``monomial_support, ``monomial_classification,
      ``monomial_projection_zero, ``homogeneousPart_eq_bot, ``component_subsingleton] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected axiom {decl}: {ax}"

#print axioms component_subsingleton
end KIP126.LinE2.StemFour
