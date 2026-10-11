import KIP126.LinProgram.Certificates.ModuleMaps.CWToCeta.Grading
import Lean.Elab.Command

/-! This audit intentionally uses non-module imports so that Lean loads proof
bodies and private helpers throughout the dependency closure. Public module
imports alone omit those values and would leave the audit incomplete. -/




/-! Independent audit of every image in the complete native CW-to-Ceta
graph and of its conditional grading restriction on the full quotient.
Relation certificates and actual spectrum-map comparison are separate. -/

open KIP126.LinModule KIP126.LinModule.NativeMapCertificates
open KIP126.LinE2.NativeModuleCertificates.Support

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod ||
        (`KIP126.Def.StableHomotopy.Implementation).isPrefixOf mod ||
        mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "CW graph grading imports a model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``nativeMonomial_smul_mem, ``homogeneousModuleTermsCheck,
      ``homogeneousModuleTermsCheck_sound, ``nativeModuleImage,
      ``nativeModuleTerms, ``evaluate_nativeModuleTerms,
      ``evaluate_termsExpression_append, ``evaluate_scaleTerms,
      ``evaluate_substituteModuleWord, ``substituteModuleRelation_words,
      ``evaluate_terms_flatMap, ``evaluate_substituteModuleRelation,
      ``evaluate_moduleRelationTerms, ``termsExpression_off_support,
      ``evaluate_restrict_terms, ``termsSupported_spec,
      ``check_terms_projection_zero, ``evaluate_single_terms_zero,
      ``CWNuEta.generatorRow_present, ``CWNuEta.generatorData, ``CWNuEta.generatorDegree,
      ``Ceta.generatorRow_present, ``Ceta.generatorData, ``Ceta.generatorDegree,
      ``CWToCeta.generatorImage, ``CWToCeta.imageTerms, ``CWToCeta.imageTerms_evaluate,
      ``cwCode_get, ``cwDegreeCheck, ``cw_degree_all, ``cw_nativeImage_mem,
      ``cw_desc_mem, ``cwDescAt, ``cwDescAt_val] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected CW grading axiom {decl}: {ax}"
  let some info := env.find? ``check_terms_projection_zero | throwError "missing proof"
  let some value := info.value? (allowOpaque := true) | throwError "missing proof value"
  unless value.getUsedConstants.contains
      ``KIP126.LinE2.NativeModuleCertificates.check_sound_projection do
    throwError "terms proof must reuse the original checker soundness"

/-- Retain integer subtraction at the source bottom cell. -/
example : CWNuEta.generatorDegree ⟨0, by decide⟩ + (0,-4) = (0,-4) := by decide

example : CWToCeta.generatorImage ⟨0, by decide⟩ = 0 := by
  unfold CWToCeta.generatorImage
  rw [cwCode_get]
  rfl

example : CWToCeta.generatorImage ⟨0, by decide⟩ ∈ Presentation.homogeneousPart
    RawData.Ceta.generatorCount RawData.Ceta.relations Ceta.generatorDegree (0,-4) := by
  have h := cw_nativeImage_mem ⟨0, by decide⟩
  have hd : CWNuEta.generatorDegree ⟨0, by decide⟩ + (0,-4) = (0,-4) := by decide
  rw [hd] at h
  exact h

#print axioms KIP126.LinModule.NativeMapCertificates.cw_degree_all
#print axioms KIP126.LinModule.NativeMapCertificates.cw_nativeImage_mem
#print axioms KIP126.LinModule.NativeMapCertificates.cwDescAt
