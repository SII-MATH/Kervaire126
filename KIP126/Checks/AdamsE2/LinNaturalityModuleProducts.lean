module

public import KIP126.LinProgram.Certificates.Products.Naturality462481Modules
public import Lean.Elab.Command

@[expose] public section


/-! Full native module quotient certificates have no actual-model delivery
or admitted mathematical premise. Record identifiers retain their native
SQLite convention and NULL generator metadata stays distinct from zero. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod || mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native module certificate imports an actual model or delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinModule.Presentation.native_relation_zero,
      ``KIP126.LinModule.Presentation.projection_ofPowers,
      ``KIP126.LinE2.NativeModuleCertificates.check_sound_projection,
      ``KIP126.LinE2.NativeModuleCertificates.ceta_check,
      ``KIP126.LinE2.NativeModuleCertificates.cw_check,
      ``KIP126.LinE2.NativeModuleCertificates.ceta_quotient_equality,
      ``KIP126.LinE2.NativeModuleCertificates.cw_quotient_equality,
      ``KIP126.LinModule.NaturalityModuleProducts.ceta13125_mem,
      ``KIP126.LinModule.NaturalityModuleProducts.ceta13126_mem,
      ``KIP126.LinModule.NaturalityModuleProducts.cw13675_mem,
      ``KIP126.LinModule.NaturalityModuleProducts.native_ceta_map_column0,
      ``KIP126.LinModule.NaturalityModuleProducts.native_cw_ancestor_product,
      ``KIP126.LinModule.NaturalityModuleProducts.native_ceta_strings,
      ``KIP126.LinModule.NaturalityModuleProducts.native_cw_strings] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do throwError "unexpected native module axiom {decl}: {ax}"

open KIP126.LinModule
set_option maxRecDepth 100000

example : Ceta.Generator = Fin 887 := rfl
example : CWNuEta.Generator = Fin 844 := rfl
example : RawData.Ceta.relationRow 13124 =
    some ⟨13125, "195,1,12;385,1,2;456,1,0", 15, 140⟩ := by rfl
example : RawData.Ceta.relationRow 13125 =
    some ⟨13126, "385,1,2;456,1,0;67,1,107,1,0", 15, 140⟩ := by rfl
example : RawData.CWNuEta.relationRow 13674 =
    some ⟨13675, "3,1,240;438,1,2;0,2,418,1,2", 16, 145⟩ := by rfl
example : RawData.CWNuEta.generatorRow 240 =
    some ⟨240, none, 7864488, 15, 137, none, none⟩ := by rfl

open KIP126.LinE2.NativeModuleCertificates NamedElementCertificates
set_option maxHeartbeats 4000000 in
example : ModuleExpressions.check [ceta13125, ceta13126] cetaInput cetaOutput
    [⟨0, [[]]⟩] = false := by decide

set_option maxHeartbeats 4000000 in
example : ModuleExpressions.check [cw13675] cwInput (slot 1 [[438]]) cwWitness = false := by
  decide

example : True := by
  fail_if_success
    have : Ceta.monomial "195,1,12" = Ceta.monomial "67,2,107,1,0" := by
      exact NaturalityModuleProducts.native_ceta_strings
  fail_if_success
    have : CWNuEta.monomial "3,1,240" = CWNuEta.monomial "438,1,2" := by
      exact NaturalityModuleProducts.native_cw_strings
  trivial

#print axioms KIP126.LinModule.NaturalityModuleProducts.native_ceta_strings
#print axioms KIP126.LinModule.NaturalityModuleProducts.native_cw_strings
