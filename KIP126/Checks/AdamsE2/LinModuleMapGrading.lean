module

public import KIP126.LinProgram.Certificates.ModuleMaps.CetaToSphere.Grading
public import Lean.Elab.Command

@[expose] public section


/-! Independent audit of the generic integer homogeneous-span construction.
The complete Ceta degree computation is included; full relation certification
and actual-model comparisons remain separate obligations. -/

open KIP126.LinModule.Presentation KIP126.LinModule.NativeMapCertificates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def.StageInput).isPrefixOf mod ||
        (`KIP126.Def.StableHomotopy.Implementation).isPrefixOf mod then
      throwError "generic module grading imports a model/delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``coefficientDegree, ``homogeneousSpan, ``homogeneousPart,
      ``coefficientDegree_add, ``coefficientDegree_zero,
      ``generator_mem_homogeneousSpan, ``monomial_smul_mem_homogeneousSpan,
      ``smul_mem_homogeneousSpan, ``map_mem_homogeneousSpan,
      ``desc_mem_homogeneousSpan, ``coefficientPart, ``coefficientPart_nat,
      ``nativeVariableDegree, ``nativeMonomialDegree, ``homogeneousPolynomialCheck,
      ``nativeMonomial_mem, ``homogeneousPolynomialCheck_sound,
      ``KIP126.LinModule.Ceta.generatorRow_present,
      ``KIP126.LinModule.Ceta.generatorData, ``KIP126.LinModule.Ceta.generatorDegree,
      ``cetaCode_get, ``cetaDegreeCheck, ``ceta_degree_all, ``ceta_nativeImage_mem,
      ``ceta_desc_mem, ``cetaDescAt, ``cetaDescAt_val,
      ``nativeImage, ``parseNativeCode, ``evaluate_parseNativeCode] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected grading axiom {decl}: {ax}"

/-- The old E2At carrier embeds using the actual submodule equality,
without any new homogeneous-basis or actual-page hypothesis. -/
example (s t : ℕ) (x : KIP126.LinE2.E2At s t) :
    x.val ∈ coefficientPart ((s : ℤ), (t : ℤ)) := by
  rw [coefficientPart_nat]
  exact x.property

example (s t : ℕ) (x : coefficientPart ((s : ℤ), (t : ℤ))) :
    x.val ∈ KIP126.LinE2.homogeneousPart s t := by
  rw [← coefficientPart_nat]
  exact x.property

#print axioms KIP126.LinModule.NativeMapCertificates.ceta_nativeImage_mem
#print axioms KIP126.LinModule.NativeMapCertificates.cetaDescAt
