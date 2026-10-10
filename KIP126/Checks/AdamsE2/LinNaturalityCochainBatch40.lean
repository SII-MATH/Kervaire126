import KIP126.LinProgram.Certificates.Naturality.CochainBatch40
import Lean.Elab.Command

/-! Finite native combinations retain all their terms and all map columns.
These checks do not identify native data with an actual Adams resolution. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Interface).isPrefixOf mod || (`KIP126.Main).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "finite native cochain certificate crossed the model boundary: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinModule.CochainMapCertificate.checkCombination_sound,
      ``KIP126.LinModule.CochainMapCertificate.checkCombination_sound_precomposition,
      ``KIP126.LinModule.CochainMapCertificate.columnValue_augmentationSupport,
      ``KIP126.LinModule.CochainMapCertificate.checkCombination_of_support,
      ``KIP126.LinModule.NaturalityCochainBatch40.augmentation_columns_match,
      ``KIP126.LinModule.NaturalityCochainBatch40.batch_checked,
      ``KIP126.LinModule.NaturalityCochainBatch40.entry_pullback,
      ``KIP126.LinModule.NaturalityCochainBatch40.entry_precomposition,
      ``KIP126.LinModule.NaturalityCochainBatch40.sphere_cochain_differential_zero,
      ``KIP126.LinModule.NaturalityCochainBatch40.ceta_cochain_differential_zero,
      ``KIP126.LinModule.NaturalityCochainBatch40.native_record_coverage,
      ``KIP126.LinModule.NaturalityCochainBatch40.requests_in_range,
      ``KIP126.LinModule.NaturalityCochainBatch40.family_bounds,
      ``KIP126.LinModule.NaturalityCochainBatch40.sphere_differentials_graded,
      ``KIP126.LinModule.NaturalityCochainBatch40.ceta_differentials_graded,
      ``KIP126.LinModule.NaturalityCochainBatch40.map_columns_graded] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in finite native cochain certificate {decl}: {ax}"

namespace KIP126.LinModule.CochainBatch40Checks
open CochainMapCertificate RawData.NaturalityCochainBatch40

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The two original endpoint records survive the enlarged global indexing. -/
example : (entries 67).nativeBasisId = 69 ∧ (entries 67).sources = [⟨19, by decide⟩] ∧
    (entries 67).targets = [⟨14, by decide⟩] ∧
    (cetaGenerators 19).id = 1048587 ∧ (sphereGenerators 14).id = 1048583 := by
  decide +kernel

example : (entries 78).nativeBasisId = 80 ∧ (entries 78).sources = [⟨84, by decide⟩] ∧
    (entries 78).targets = [⟨56, by decide⟩] ∧
    (cetaGenerators 84).id = 2621447 ∧ (sphereGenerators 56).id = 2621443 := by
  decide +kernel

/-- A genuine three-term source is kept, even though its full image is zero. -/
example : (entries 104).nativeBasisId = 106 ∧
    (entries 104).sources = [⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩] ∧
    (entries 104).targets = [] := by decide +kernel

/-- The degree window now contains a genuine two-term output. -/
example : (entries 102).nativeBasisId = 104 ∧
    (entries 102).targets = [⟨43, by decide⟩, ⟨44, by decide⟩] := by decide +kernel

/-- Deleting either output summand changes the finite equality. -/
example : checkCombination mapColumns
    { entries 102 with targets := [⟨43, by decide⟩] } = false := by decide +kernel

/-- Dropping a source summand also changes the equation. -/
example : checkCombination mapColumns
    { entries 104 with sources := [⟨63, by decide⟩, ⟨64, by decide⟩] } = false := by
  decide +kernel

/-- Generic list semantics is genuinely F2-linear, including cancellation. -/
example : checkCombination mapColumns
    { sources := [⟨64, by decide⟩, ⟨64, by decide⟩], targets := [], nativeBasisId := 0 } = true := by
  decide +kernel

end KIP126.LinModule.CochainBatch40Checks

#print axioms KIP126.LinModule.NaturalityCochainBatch40.entry_precomposition
#print axioms KIP126.LinModule.NaturalityCochainBatch40.ceta_cochain_differential_zero
