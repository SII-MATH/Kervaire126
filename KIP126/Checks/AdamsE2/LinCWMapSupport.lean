import KIP126.LinProgram.Certificates.ModuleMaps.CWMaxSupport
import Lean.Elab.Command

/-! This audit intentionally uses non-module imports so that Lean loads proof
bodies and private helpers throughout the dependency closure. Public module
imports alone omit those values and would leave the audit incomplete. -/




open KIP126.LinE2.NativeModuleCertificates.Support
open KIP126.LinModule.CWMaxSupport
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod || mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "module support certificate imports a model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``nativeModuleImage_empty, ``embed_apply, ``evaluate_restrict,
      ``evaluate_embed, ``check_sound_embed_projection, ``check_sound_restrict_projection,
      ``supportEmbedding, ``checker, ``relation_values, ``full_887_equality,
      ``source_relation_mem, ``native_image766, ``native_image196, ``native_image187,
      ``row67028_image_zero, ``source_relation_row, ``native_empty_image] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected module support axiom: {decl}: {ax}"
  -- Demand use of the unchanged full-target soundness adapter and original
  -- checker. No independent compressed quotient model is constructed.
  let some info := env.find? ``full_887_equality | throwError "missing full-target equality"
  let some value := info.value? (allowOpaque := true) | throwError "missing full-target proof"
  unless value.getUsedConstants.contains ``check_sound_embed_projection do
    throwError "real row no longer uses the full-target support adapter"
  let some info := env.find? ``check_sound_embed_projection | throwError "missing support adapter"
  let some value := info.value? (allowOpaque := true) | throwError "missing support proof"
  unless value.getUsedConstants.contains ``KIP126.LinE2.NativeModuleCertificates.check_sound_projection do
    throwError "support adapter no longer reuses the existing checker soundness"

#print axioms KIP126.LinModule.CWMaxSupport.row67028_image_zero
#print axioms KIP126.LinE2.NativeModuleCertificates.Support.check_sound_restrict_projection
