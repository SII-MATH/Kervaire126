import KIP126.LinProgram.Generated.Naturality.Words200.Shard093
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard093
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard093
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
  exact ⟨Shared.RelationChunk000.relation5_zero, Shared.RelationChunk000.relation22_zero, Shared.RelationChunk000.relation61_zero, Shared.RelationChunk000.relation62_zero, Shared.RelationChunk032.relation1352_zero, Shared.RelationChunk034.relation1395_zero, Shared.RelationChunk034.relation1396_zero, Shared.RelationChunk034.relation1397_zero, Shared.RelationChunk034.relation1398_zero, Shared.RelationChunk034.relation1400_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11906 128 := by cbv
private def targetRows : List BasisRow := [⟨13, 180, 3, "0,1,8,1,20,1,324,1"⟩,
  ⟨12, 180, 0, "3,1,790,1"⟩,
  ⟨12, 180, 1, "3,1,789,1"⟩,
  ⟨12, 180, 2, "0,1,884,1"⟩,
  ⟨12, 180, 3, "0,1,45,1,324,1"⟩,
  ⟨11, 180, 0, "3,1,792,1"⟩,
  ⟨11, 180, 1, "3,1,791,1"⟩,
  ⟨11, 180, 2, "0,2,7,1,676,1"⟩,
  ⟨10, 180, 0, "43,1,368,1"⟩,
  ⟨10, 180, 1, "1,1,7,1,676,1"⟩,
  ⟨10, 180, 2, "0,4,18,1,506,1"⟩,
  ⟨9, 180, 1, "3,1,794,1"⟩,
  ⟨9, 180, 2, "0,1,885,1"⟩,
  ⟨8, 180, 1, "7,1,698,1"⟩,
  ⟨8, 180, 2, "1,2,18,1,506,1"⟩,
  ⟨8, 180, 3, "0,2,8,1,18,1,324,1"⟩,
  ⟨8, 180, 4, "0,4,849,1"⟩,
  ⟨7, 180, 0, "2,1,18,1,506,1"⟩,
  ⟨7, 180, 2, "0,4,850,1"⟩,
  ⟨6, 180, 0, "2,1,43,1,324,1"⟩,
  ⟨5, 180, 0, "3,1,38,1,324,1"⟩,
  ⟨5, 180, 1, "2,1,849,1"⟩,
  ⟨4, 180, 0, "2,1,850,1"⟩,
  ⟨181, 181, 0, "0,181"⟩,
  ⟨60, 181, 0, "1,1,870,1"⟩,
  ⟨57, 181, 0, "0,1,8,1,661,1"⟩,
  ⟨56, 181, 0, "0,1,16,1,554,1"⟩,
  ⟨55, 181, 0, "0,1,17,1,554,1"⟩,
  ⟨54, 181, 0, "0,53,324,1"⟩,
  ⟨47, 181, 0, "0,1,8,1,662,1"⟩,
  ⟨46, 181, 0, "0,1,8,1,663,1"⟩,
  ⟨46, 181, 1, "0,2,871,1"⟩,
  ⟨45, 181, 0, "0,1,17,1,556,1"⟩,
  ⟨43, 181, 0, "0,7,64,1,224,1"⟩,
  ⟨42, 181, 0, "0,7,64,1,225,1"⟩,
  ⟨40, 181, 0, "0,7,807,1"⟩,
  ⟨39, 181, 1, "0,8,795,1"⟩,
  ⟨37, 181, 0, "0,1,16,1,64,1,137,1"⟩,
  ⟨36, 181, 0, "0,1,16,1,64,1,138,1"⟩,
  ⟨36, 181, 1, "0,2,64,1,244,1"⟩,
  ⟨36, 181, 2, "0,2,8,2,491,1"⟩,
  ⟨35, 181, 1, "0,2,138,1,149,1"⟩,
  ⟨35, 181, 2, "0,2,16,1,17,1,260,1"⟩,
  ⟨34, 181, 0, "0,2,17,2,260,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row7131_mem, Shared.BasisChunk006.row7132_mem, Shared.BasisChunk006.row7133_mem, Shared.BasisChunk006.row7134_mem, Shared.BasisChunk006.row7135_mem, Shared.BasisChunk006.row7136_mem, Shared.BasisChunk006.row7137_mem, Shared.BasisChunk006.row7138_mem, Shared.BasisChunk006.row7139_mem, Shared.BasisChunk006.row7140_mem, Shared.BasisChunk006.row7141_mem, Shared.BasisChunk006.row7143_mem, Shared.BasisChunk006.row7144_mem, Shared.BasisChunk006.row7146_mem, Shared.BasisChunk006.row7147_mem, Shared.BasisChunk006.row7148_mem, Shared.BasisChunk006.row7149_mem, Shared.BasisChunk006.row7150_mem, Shared.BasisChunk006.row7152_mem, Shared.BasisChunk006.row7153_mem, Shared.BasisChunk006.row7155_mem, Shared.BasisChunk006.row7156_mem, Shared.BasisChunk006.row7158_mem, Shared.BasisChunk006.row7159_mem, Shared.BasisChunk006.row7160_mem, Shared.BasisChunk006.row7161_mem, Shared.BasisChunk006.row7162_mem, Shared.BasisChunk006.row7163_mem, Shared.BasisChunk006.row7164_mem, Shared.BasisChunk006.row7165_mem, Shared.BasisChunk006.row7166_mem, Shared.BasisChunk006.row7167_mem, Shared.BasisChunk007.row7168_mem, Shared.BasisChunk007.row7169_mem, Shared.BasisChunk007.row7170_mem, Shared.BasisChunk007.row7171_mem, Shared.BasisChunk007.row7173_mem, Shared.BasisChunk007.row7174_mem, Shared.BasisChunk007.row7175_mem, Shared.BasisChunk007.row7176_mem, Shared.BasisChunk007.row7177_mem, Shared.BasisChunk007.row7179_mem, Shared.BasisChunk007.row7180_mem, Shared.BasisChunk007.row7181_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard093
