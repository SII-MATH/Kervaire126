import KIP126.Def.Steenrod.MilnorModule.Resolution.Raw.Proofs
import Lean.Elab.Command

/-! This audit intentionally uses non-module imports so that Lean loads proof
bodies and private helpers throughout the dependency closure. Public module
imports alone omit those values and would leave the audit incomplete. -/




/-! Local chain identities are proved, while their specified dualization still
has inherited proof debt. This audit rejects direct admissions in the new
bodies and project axioms; it deliberately does not certify the dependencies. -/
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  for decl in [``KIP126.Steenrod.Milnor.Module.dualLeftMap_comp,
      ``KIP126.Steenrod.Milnor.Module.dualLeftMap_zero,
      ``KIP126.Steenrod.Milnor.Module.dualCobarDifferential_shape,
      ``KIP126.Steenrod.Milnor.Module.dualCobarDifferential_comp,
      ``KIP126.Steenrod.Milnor.Module.dualCobarDifferential_augmentation] do
    let info ← getConstInfo decl
    let some value := info.value? (allowOpaque := true) |
      throwError "missing local dualization proof: {decl}"
    if value.getUsedConstants.contains ``sorryAx then
      throwError "direct admission in local dualization proof: {decl}"
    for ax in ← collectAxioms decl do
      unless allowed.contains ax do
        throwError "unexpected dualization axiom: {decl}: {ax}"
  for mod in (← getEnv).allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic dualization imported delivery or program data: {mod}"

#print axioms KIP126.Steenrod.Milnor.Module.dualCobarDifferential_shape
#print axioms KIP126.Steenrod.Milnor.Module.dualCobarDifferential_comp
#print axioms KIP126.Steenrod.Milnor.Module.dualCobarDifferential_augmentation
