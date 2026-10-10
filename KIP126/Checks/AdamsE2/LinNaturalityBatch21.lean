import KIP126.LinProgram.Certificates.Naturality.Batch21
import Lean.Elab.Command

/-! Regression checks for the finite batch certificate boundary. Target lists
encode sums, including zero; stored coordinate IDs are not nonvanishing claims.
The checks exercise both direct evaluation and the necessary relation witness. -/
namespace KIP126.Checks.LinNaturalityBatch21
open KIP126.LinModule.BatchMapCertificate
open KIP126.LinModule.RawData.NaturalityBatch21

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
attribute [local cbv_eval] KIP126.LinModule.NativeMapCertificates.cetaCode_get
  KIP126.LinE2.generatorDegree_eq_row
  KIP126.LinE2.SquareDetection.splitOn_comma
  KIP126.LinE2.SquareDetection.splitOn_semicolon
  KIP126.LinE2.SquareDetection.toNat?_eq_chars

/-- Original row 43 needs the sphere relation x₂³ + x₁²x₃ = 0. -/
def relationSample : Entry where
  source := ⟨43, 3, 14, 0, "2,2,2"⟩
  targetS := 3
  targetT := 12
  targets := [⟨25, 3, 12, 0, "1,2,3,1"⟩]
  witness := [⟨0, [[]]⟩]

example : relationSample ∈ entries := by
  simp [relationSample, entries]
example : check relationCodes relationSample = true := by cbv
example : check relationCodes { relationSample with witness := [] } = false := by cbv
example : check [] relationSample = false := by cbv
example : check relationCodes { relationSample with witness := [⟨1, [[]]⟩] } = false := by cbv
example : check relationCodes { relationSample with witness := [⟨0, [[0]]⟩] } = false := by cbv
example : check relationCodes { relationSample with targets := [] } = false := by cbv
example : check relationCodes { relationSample with
    targets := [⟨25, 3, 12, 0, "unknown,2,3,1"⟩] } = false := by cbv
example : check relationCodes { relationSample with
    targets := [⟨25, 3, 12, 0, ""⟩] } = false := by cbv
example : check relationCodes { relationSample with
    targets := [⟨25, 3, 12, 0, "1,2,3,1;"⟩] } = false := by cbv
example : check relationCodes { relationSample with
    targets := [⟨25, 3, 12, 0, "1,2,3"⟩] } = false := by cbv
example : check relationCodes { relationSample with
    targets := [⟨25, 3, 12, 0, "2914,2,3,1"⟩] } = false := by cbv
example : check relationCodes { relationSample with targetT := 11 } = false := by cbv
example : check relationCodes { relationSample with
    source := { relationSample.source with code := "2,2,887" } } = false := by cbv

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "native batch imports actual-model delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinModule.BatchMapCertificate.check_sound,
      ``KIP126.LinModule.BatchMapCertificate.check_sound_desc,
      ``KIP126.LinModule.NaturalityBatch21.relation_mem,
      ``KIP126.LinModule.NaturalityBatch21.relations_zero,
      ``KIP126.LinModule.NaturalityBatch21.all_checks,
      ``KIP126.LinModule.NaturalityBatch21.entry_evaluate,
      ``KIP126.LinModule.NaturalityBatch21.zero_evaluate,
      ``KIP126.LinModule.NaturalityBatch21.entry_desc,
      ``KIP126.LinModule.NaturalityBatch21.target_row_mem,
      ``KIP126.LinModule.NaturalityBatch21.entry_count,
      ``KIP126.LinModule.NaturalityBatch21.zero_count,
      ``KIP126.LinModule.NaturalityBatch21.singleton_count,
      ``KIP126.LinModule.NaturalityBatch21.relation_witness_count] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native batch certificate {decl}: {ax}"

#print axioms KIP126.LinModule.NaturalityBatch21.entry_evaluate
#print axioms KIP126.LinModule.NaturalityBatch21.zero_evaluate
#print axioms KIP126.LinModule.NaturalityBatch21.entry_desc
#print axioms KIP126.LinModule.NaturalityBatch21.target_row_mem
end KIP126.Checks.LinNaturalityBatch21
