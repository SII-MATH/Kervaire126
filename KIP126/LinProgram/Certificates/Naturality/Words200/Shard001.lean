module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard001
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard001
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe
theorem relations_zero : ∀ code ∈ relationCodes, nativeImage code = 0 := by
  simp only [relationCodes, List.forall_mem_cons]
  exact ⟨Shared.RelationChunk000.relation16_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 130 128 := by cbv
private def targetRows : List BasisRow := [⟨6, 26, 0, "0,2,13,1"⟩,
  ⟨5, 26, 0, "1,1,13,1"⟩,
  ⟨4, 26, 0, "2,1,11,1"⟩,
  ⟨27, 27, 0, "0,27"⟩,
  ⟨28, 28, 0, "0,28"⟩,
  ⟨9, 28, 0, "15,1"⟩,
  ⟨5, 28, 0, "2,1,13,1"⟩,
  ⟨29, 29, 0, "0,29"⟩,
  ⟨10, 29, 0, "0,1,15,1"⟩,
  ⟨6, 29, 0, "0,1,2,1,13,1"⟩,
  ⟨5, 29, 0, "1,1,4,1,7,1"⟩,
  ⟨30, 30, 0, "0,30"⟩,
  ⟨11, 30, 0, "0,2,15,1"⟩,
  ⟨7, 30, 0, "17,1"⟩,
  ⟨31, 31, 0, "0,31"⟩,
  ⟨9, 31, 0, "0,1,16,1"⟩,
  ⟨8, 31, 0, "0,1,17,1"⟩,
  ⟨32, 32, 0, "0,32"⟩,
  ⟨10, 32, 0, "0,2,16,1"⟩,
  ⟨9, 32, 1, "0,2,17,1"⟩,
  ⟨6, 32, 0, "2,2,13,1"⟩,
  ⟨33, 33, 0, "0,33"⟩,
  ⟨10, 33, 0, "0,3,17,1"⟩,
  ⟨7, 33, 0, "20,1"⟩,
  ⟨3, 33, 0, "0,1,7,2"⟩,
  ⟨2, 33, 0, "0,1,18,1"⟩,
  ⟨34, 34, 0, "0,34"⟩,
  ⟨11, 34, 0, "0,4,17,1"⟩,
  ⟨9, 34, 0, "0,1,19,1"⟩,
  ⟨8, 34, 0, "0,1,20,1"⟩,
  ⟨4, 34, 0, "0,2,7,2"⟩,
  ⟨3, 34, 0, "1,1,7,2"⟩,
  ⟨3, 34, 1, "0,2,18,1"⟩,
  ⟨35, 35, 0, "0,35"⟩,
  ⟨12, 35, 0, "0,5,17,1"⟩,
  ⟨10, 35, 0, "0,2,19,1"⟩,
  ⟨9, 35, 0, "0,2,20,1"⟩,
  ⟨5, 35, 0, "0,3,7,2"⟩,
  ⟨4, 35, 0, "0,3,18,1"⟩,
  ⟨36, 36, 0, "0,36"⟩,
  ⟨11, 36, 0, "0,3,19,1"⟩,
  ⟨7, 36, 0, "22,1"⟩,
  ⟨6, 36, 0, "23,1"⟩,
  ⟨5, 36, 0, "24,1"⟩,
  ⟨5, 36, 1, "0,4,18,1"⟩,
  ⟨2, 36, 0, "2,1,18,1"⟩,
  ⟨37, 37, 0, "0,37"⟩,
  ⟨12, 37, 0, "1,1,21,1"⟩,
  ⟨9, 37, 0, "0,1,8,2"⟩,
  ⟨8, 37, 0, "0,1,22,1"⟩,
  ⟨7, 37, 0, "0,1,23,1"⟩,
  ⟨6, 37, 0, "0,5,18,1"⟩,
  ⟨4, 37, 0, "26,1"⟩,
  ⟨3, 37, 0, "0,1,2,1,18,1"⟩,
  ⟨38, 38, 0, "0,38"⟩,
  ⟨10, 38, 0, "0,2,8,2"⟩,
  ⟨9, 38, 0, "0,2,22,1"⟩,
  ⟨8, 38, 0, "0,2,23,1"⟩,
  ⟨7, 38, 0, "0,6,18,1"⟩,
  ⟨5, 38, 0, "0,1,26,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row79_mem, Shared.BasisChunk000.row80_mem, Shared.BasisChunk000.row81_mem, Shared.BasisChunk000.row82_mem, Shared.BasisChunk000.row84_mem, Shared.BasisChunk000.row86_mem, Shared.BasisChunk000.row87_mem, Shared.BasisChunk000.row88_mem, Shared.BasisChunk000.row89_mem, Shared.BasisChunk000.row90_mem, Shared.BasisChunk000.row91_mem, Shared.BasisChunk000.row92_mem, Shared.BasisChunk000.row93_mem, Shared.BasisChunk000.row95_mem, Shared.BasisChunk000.row96_mem, Shared.BasisChunk000.row97_mem, Shared.BasisChunk000.row98_mem, Shared.BasisChunk000.row99_mem, Shared.BasisChunk000.row100_mem, Shared.BasisChunk000.row102_mem, Shared.BasisChunk000.row103_mem, Shared.BasisChunk000.row106_mem, Shared.BasisChunk000.row107_mem, Shared.BasisChunk000.row109_mem, Shared.BasisChunk000.row110_mem, Shared.BasisChunk000.row111_mem, Shared.BasisChunk000.row112_mem, Shared.BasisChunk000.row113_mem, Shared.BasisChunk000.row115_mem, Shared.BasisChunk000.row116_mem, Shared.BasisChunk000.row117_mem, Shared.BasisChunk000.row118_mem, Shared.BasisChunk000.row119_mem, Shared.BasisChunk000.row121_mem, Shared.BasisChunk000.row122_mem, Shared.BasisChunk000.row124_mem, Shared.BasisChunk000.row125_mem, Shared.BasisChunk000.row126_mem, Shared.BasisChunk000.row127_mem, Shared.BasisChunk000.row128_mem, Shared.BasisChunk000.row129_mem, Shared.BasisChunk000.row131_mem, Shared.BasisChunk000.row132_mem, Shared.BasisChunk000.row133_mem, Shared.BasisChunk000.row134_mem, Shared.BasisChunk000.row137_mem, Shared.BasisChunk000.row138_mem, Shared.BasisChunk000.row139_mem, Shared.BasisChunk000.row140_mem, Shared.BasisChunk000.row141_mem, Shared.BasisChunk000.row142_mem, Shared.BasisChunk000.row143_mem, Shared.BasisChunk000.row144_mem, Shared.BasisChunk000.row145_mem, Shared.BasisChunk000.row146_mem, Shared.BasisChunk000.row148_mem, Shared.BasisChunk000.row149_mem, Shared.BasisChunk000.row150_mem, Shared.BasisChunk000.row151_mem, Shared.BasisChunk000.row153_mem, by simp⟩
private def targetCheck (r : BasisRecord) : Bool :=
  targetRows.any (fun b => decide (b.s = r.s ∧ b.t = r.t ∧
    b.index = r.localIndex ∧ b.monomial = r.code))
private theorem targetCheck_sound (r : BasisRecord) (h : targetCheck r = true) :
    basisRow r ∈ basisRows := by
  obtain ⟨b, hb, h⟩ := List.any_eq_true.mp h
  simp only [decide_eq_true_eq] at h
  have he : b = basisRow r := by cases b; cases r; simp_all [basisRow]
  rw [← he]
  exact targetRows_mem b hb
private theorem targets_checked : entries.all (fun e => e.targets.all targetCheck) = true := by cbv
theorem targets_mem (e : Entry) (he : e ∈ entries) (r : BasisRecord) (hr : r ∈ e.targets) :
    basisRow r ∈ basisRows :=
  targetCheck_sound r ((List.all_eq_true.mp ((List.all_eq_true.mp targets_checked) e he)) r hr)
def certificate : CertifiedBatch :=
  ⟨relationCodes, entries, all_checks, relations_zero, targets_mem⟩
end KIP126.LinModule.NaturalityWords200.Shard001
