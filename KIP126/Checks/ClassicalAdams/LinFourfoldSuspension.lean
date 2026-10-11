module

public import KIP126.Def.ClassicalAdams.Suspension.Fourfold.Proofs
public import Lean.Elab.Command

@[expose] public section


open KIP126.Classical.Adams.Suspension.Fourfold

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic fourfold suspension imports a stage or native artifact: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``quadShift, ``quadShiftIso, ``quadShiftIso_hom, ``quadShiftIso_inv,
      ``desuspendFourInternalPage, ``desuspendFourInternalPage_hasDifferential,
      ``hasDifferential_desuspendFour] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in fourfold suspension {decl}: {ax}"

#print axioms quadShiftIso
#print axioms desuspendFourInternalPage_hasDifferential
#print axioms hasDifferential_desuspendFour
