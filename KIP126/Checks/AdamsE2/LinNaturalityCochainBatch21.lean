import KIP126.LinProgram.Certificates.Naturality.CochainBatch21
import Lean.Elab.Command

/-! Kernel-certified finite native linear algebra. These checks do not claim
Steenrod chain-map correctness, exactness, or comparison with actual spectra. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "finite native cochain certificate crossed the model boundary: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinModule.CochainMapCertificate.check_sound,
      ``KIP126.LinModule.CochainMapCertificate.functional_pullback,
      ``KIP126.LinModule.CochainMapCertificate.check_sound_precomposition,
      ``KIP126.LinModule.CochainMapCertificate.pullback_eq_zero_of_minimalCheck,
      ``KIP126.LinModule.NaturalityCochainBatch21.batch_checked,
      ``KIP126.LinModule.NaturalityCochainBatch21.entry_pullback,
      ``KIP126.LinModule.NaturalityCochainBatch21.entry_precomposition,
      ``KIP126.LinModule.NaturalityCochainBatch21.sphere_cochain_differential_zero,
      ``KIP126.LinModule.NaturalityCochainBatch21.ceta_cochain_differential_zero,
      ``KIP126.LinModule.NaturalityCochainBatch21.entries_cover,
      ``KIP126.LinModule.NaturalityCochainBatch21.sphere_differentials_graded,
      ``KIP126.LinModule.NaturalityCochainBatch21.ceta_differentials_graded,
      ``KIP126.LinModule.NaturalityCochainBatch21.map_columns_graded] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in finite native cochain certificate {decl}: {ax}"

namespace KIP126.LinModule.CochainBatch21Checks
open CochainMapCertificate RawData.NaturalityCochainBatch21

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Original native record 69 is included, with its two global chain IDs. -/
example : (entries 67).nativeBasisId = 69 ∧
    (cetaGenerators (entries 67).source).id = 1048587 ∧
    (entries 67).targets = [⟨13, by decide⟩] ∧
    (sphereGenerators 13).id = 1048583 := by decide +kernel

/-- Original native record 80 is included with the same full source/target families. -/
example : (entries 78).nativeBasisId = 80 ∧
    (cetaGenerators (entries 78).source).id = 2621447 ∧
    (entries 78).targets = [⟨30, by decide⟩] ∧
    (sphereGenerators 30).id = 2621443 := by decide +kernel

/-- Deleting the nonzero image of record 69 is detected. -/
example : check mapColumns { entries 67 with targets := [] } = false := by
  decide +kernel

/-- Replacing that image by an unrelated sphere coordinate is detected. -/
example : check mapColumns { entries 67 with targets := [⟨30, by decide⟩] } = false := by
  decide +kernel

/-- A coefficient of degree zero prevents the positivity certificate. -/
example : minimalCheck (fun _ : Fin 1 => [({ powers := [0], generator := ⟨0, by decide⟩ } :
    Term 1)]) = false := by decide +kernel

end KIP126.LinModule.CochainBatch21Checks

#print axioms KIP126.LinModule.NaturalityCochainBatch21.entry_precomposition
#print axioms KIP126.LinModule.NaturalityCochainBatch21.ceta_cochain_differential_zero
