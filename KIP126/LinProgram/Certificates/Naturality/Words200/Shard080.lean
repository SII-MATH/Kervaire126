import KIP126.LinProgram.Generated.Naturality.Words200.Shard080
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk027
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard080
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard080
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
  exact ⟨Shared.RelationChunk000.relation45_zero, Shared.RelationChunk000.relation46_zero, Shared.RelationChunk002.relation244_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation282_zero, Shared.RelationChunk027.relation1141_zero, Shared.RelationChunk027.relation1156_zero, Shared.RelationChunk027.relation1158_zero, Shared.RelationChunk027.relation1159_zero, Shared.RelationChunk027.relation1160_zero, Shared.RelationChunk027.relation1161_zero, Shared.RelationChunk027.relation1162_zero, Shared.RelationChunk027.relation1163_zero, Shared.RelationChunk027.relation1164_zero, Shared.RelationChunk027.relation1165_zero, Shared.RelationChunk027.relation1166_zero, Shared.RelationChunk027.relation1167_zero, Shared.RelationChunk027.relation1169_zero, Shared.RelationChunk027.relation1170_zero, Shared.RelationChunk027.relation1171_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10242 128 := by cbv
private def targetRows : List BasisRow := [⟨31, 172, 0, "0,2,8,1,17,1,278,1"⟩,
  ⟨26, 172, 0, "784,1"⟩,
  ⟨25, 172, 0, "13,1,537,1"⟩,
  ⟨25, 172, 1, "13,4,105,1"⟩,
  ⟨24, 172, 0, "13,1,538,1"⟩,
  ⟨24, 172, 1, "9,1,13,2,23,1,75,1"⟩,
  ⟨23, 172, 1, "2,1,737,1"⟩,
  ⟨22, 172, 1, "8,1,69,1,147,1"⟩,
  ⟨22, 172, 2, "0,1,8,1,582,1"⟩,
  ⟨22, 172, 3, "0,2,64,1,209,1"⟩,
  ⟨21, 172, 1, "0,1,17,1,475,1"⟩,
  ⟨21, 172, 2, "0,2,760,1"⟩,
  ⟨20, 172, 0, "1,1,760,1"⟩,
  ⟨20, 172, 1, "0,1,780,1"⟩,
  ⟨19, 172, 0, "23,1,417,1"⟩,
  ⟨19, 172, 1, "1,1,761,1"⟩,
  ⟨19, 172, 2, "0,1,43,1,285,1"⟩,
  ⟨19, 172, 3, "0,1,3,2,604,1"⟩,
  ⟨19, 172, 4, "0,2,762,1"⟩,
  ⟨18, 172, 1, "24,1,417,1"⟩,
  ⟨18, 172, 3, "1,1,762,1"⟩,
  ⟨18, 172, 4, "0,2,763,1"⟩,
  ⟨17, 172, 0, "0,2,764,1"⟩,
  ⟨17, 172, 1, "0,5,732,1"⟩,
  ⟨16, 172, 0, "9,1,569,1"⟩,
  ⟨16, 172, 2, "0,2,766,1"⟩,
  ⟨15, 172, 1, "0,1,74,1,197,1"⟩,
  ⟨15, 172, 2, "0,2,31,1,324,1"⟩,
  ⟨15, 172, 3, "0,4,743,1"⟩,
  ⟨14, 172, 2, "0,12,18,1,324,1"⟩,
  ⟨12, 172, 1, "0,2,18,1,443,1"⟩,
  ⟨11, 172, 0, "790,1"⟩,
  ⟨11, 172, 2, "2,1,746,1"⟩,
  ⟨11, 172, 3, "0,2,18,1,445,1"⟩,
  ⟨11, 172, 4, "0,2,8,1,13,1,324,1"⟩,
  ⟨10, 172, 2, "791,1"⟩,
  ⟨10, 172, 3, "0,2,32,1,324,1"⟩,
  ⟨9, 172, 0, "3,1,696,1"⟩,
  ⟨9, 172, 1, "2,2,18,1,368,1"⟩,
  ⟨9, 172, 2, "1,2,747,1"⟩,
  ⟨9, 172, 3, "0,2,18,1,446,1"⟩,
  ⟨9, 172, 4, "0,4,750,1"⟩,
  ⟨8, 172, 0, "794,1"⟩,
  ⟨8, 172, 1, "1,1,33,1,324,1"⟩,
  ⟨8, 172, 3, "1,2,749,1"⟩,
  ⟨8, 172, 4, "0,2,34,1,324,1"⟩,
  ⟨8, 172, 5, "0,4,751,1"⟩,
  ⟨7, 172, 2, "1,1,34,1,324,1"⟩,
  ⟨6, 172, 1, "1,2,751,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row6123_mem, Shared.BasisChunk005.row6124_mem, Shared.BasisChunk005.row6125_mem, Shared.BasisChunk005.row6126_mem, Shared.BasisChunk005.row6128_mem, Shared.BasisChunk005.row6129_mem, Shared.BasisChunk005.row6131_mem, Shared.BasisChunk005.row6133_mem, Shared.BasisChunk005.row6134_mem, Shared.BasisChunk005.row6135_mem, Shared.BasisChunk005.row6137_mem, Shared.BasisChunk005.row6138_mem, Shared.BasisChunk005.row6139_mem, Shared.BasisChunk005.row6140_mem, Shared.BasisChunk005.row6141_mem, Shared.BasisChunk005.row6142_mem, Shared.BasisChunk005.row6143_mem, Shared.BasisChunk006.row6144_mem, Shared.BasisChunk006.row6145_mem, Shared.BasisChunk006.row6147_mem, Shared.BasisChunk006.row6149_mem, Shared.BasisChunk006.row6150_mem, Shared.BasisChunk006.row6151_mem, Shared.BasisChunk006.row6152_mem, Shared.BasisChunk006.row6153_mem, Shared.BasisChunk006.row6155_mem, Shared.BasisChunk006.row6157_mem, Shared.BasisChunk006.row6158_mem, Shared.BasisChunk006.row6159_mem, Shared.BasisChunk006.row6162_mem, Shared.BasisChunk006.row6165_mem, Shared.BasisChunk006.row6166_mem, Shared.BasisChunk006.row6168_mem, Shared.BasisChunk006.row6169_mem, Shared.BasisChunk006.row6170_mem, Shared.BasisChunk006.row6173_mem, Shared.BasisChunk006.row6174_mem, Shared.BasisChunk006.row6175_mem, Shared.BasisChunk006.row6176_mem, Shared.BasisChunk006.row6177_mem, Shared.BasisChunk006.row6178_mem, Shared.BasisChunk006.row6179_mem, Shared.BasisChunk006.row6180_mem, Shared.BasisChunk006.row6181_mem, Shared.BasisChunk006.row6183_mem, Shared.BasisChunk006.row6184_mem, Shared.BasisChunk006.row6185_mem, Shared.BasisChunk006.row6188_mem, Shared.BasisChunk006.row6190_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard080
