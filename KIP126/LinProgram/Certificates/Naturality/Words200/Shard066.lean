import KIP126.LinProgram.Generated.Naturality.Words200.Shard066
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard066
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard066
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
  exact ⟨Shared.RelationChunk012.relation647_zero, Shared.RelationChunk020.relation937_zero, Shared.RelationChunk020.relation939_zero, Shared.RelationChunk020.relation940_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8450 128 := by cbv
private def targetRows : List BasisRow := [⟨19, 162, 0, "668,1"⟩,
  ⟨19, 162, 1, "2,1,628,1"⟩,
  ⟨19, 162, 2, "0,1,656,1"⟩,
  ⟨18, 162, 0, "13,1,23,1,190,1"⟩,
  ⟨18, 162, 1, "1,1,48,1,209,1"⟩,
  ⟨18, 162, 2, "0,2,648,1"⟩,
  ⟨17, 162, 0, "9,1,474,1"⟩,
  ⟨17, 162, 2, "0,2,650,1"⟩,
  ⟨16, 162, 0, "16,1,367,1"⟩,
  ⟨16, 162, 1, "2,1,630,1"⟩,
  ⟨15, 162, 0, "670,1"⟩,
  ⟨15, 162, 2, "17,1,367,1"⟩,
  ⟨14, 162, 0, "672,1"⟩,
  ⟨14, 162, 2, "0,2,652,1"⟩,
  ⟨13, 162, 0, "8,1,504,1"⟩,
  ⟨13, 162, 2, "0,3,18,1,314,1"⟩,
  ⟨12, 162, 1, "13,1,445,1"⟩,
  ⟨12, 162, 3, "0,2,68,1,163,1"⟩,
  ⟨12, 162, 4, "0,4,17,1,324,1"⟩,
  ⟨11, 162, 0, "675,1"⟩,
  ⟨11, 162, 3, "0,1,658,1"⟩,
  ⟨11, 162, 4, "0,1,19,1,69,2"⟩,
  ⟨11, 162, 5, "0,1,18,1,333,1"⟩,
  ⟨10, 162, 0, "18,1,338,1"⟩,
  ⟨10, 162, 1, "0,1,659,1"⟩,
  ⟨10, 162, 2, "0,1,20,1,69,2"⟩,
  ⟨10, 162, 3, "0,1,19,1,324,1"⟩,
  ⟨9, 162, 0, "0,1,20,1,324,1"⟩,
  ⟨7, 162, 1, "0,2,7,1,508,1"⟩,
  ⟨6, 162, 0, "1,1,7,1,508,1"⟩,
  ⟨6, 162, 1, "0,1,660,1"⟩,
  ⟨5, 162, 0, "18,1,341,1"⟩,
  ⟨5, 162, 1, "0,2,7,2,324,1"⟩,
  ⟨4, 162, 0, "1,1,7,2,324,1"⟩,
  ⟨4, 162, 1, "0,2,18,1,324,1"⟩,
  ⟨163, 163, 0, "0,163"⟩,
  ⟨53, 163, 0, "0,1,661,1"⟩,
  ⟨52, 163, 0, "0,7,606,1"⟩,
  ⟨49, 163, 0, "0,1,8,2,295,1"⟩,
  ⟨48, 163, 0, "0,1,8,2,296,1"⟩,
  ⟨46, 163, 0, "0,4,635,1"⟩,
  ⟨45, 163, 0, "0,4,636,1"⟩,
  ⟨43, 163, 0, "0,1,662,1"⟩,
  ⟨42, 163, 0, "0,1,663,1"⟩,
  ⟨39, 163, 0, "0,1,8,2,297,1"⟩,
  ⟨38, 163, 0, "0,1,8,2,298,1"⟩,
  ⟨37, 163, 0, "0,1,8,1,17,1,238,1"⟩,
  ⟨37, 163, 1, "0,19,500,1"⟩,
  ⟨36, 163, 0, "0,35,324,1"⟩,
  ⟨32, 163, 0, "0,2,8,1,491,1"⟩,
  ⟨31, 163, 0, "0,1,664,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row5086_mem, Shared.BasisChunk004.row5087_mem, Shared.BasisChunk004.row5088_mem, Shared.BasisChunk004.row5089_mem, Shared.BasisChunk004.row5090_mem, Shared.BasisChunk004.row5091_mem, Shared.BasisChunk004.row5092_mem, Shared.BasisChunk004.row5094_mem, Shared.BasisChunk004.row5095_mem, Shared.BasisChunk004.row5096_mem, Shared.BasisChunk004.row5097_mem, Shared.BasisChunk004.row5099_mem, Shared.BasisChunk004.row5100_mem, Shared.BasisChunk004.row5102_mem, Shared.BasisChunk004.row5103_mem, Shared.BasisChunk004.row5105_mem, Shared.BasisChunk004.row5107_mem, Shared.BasisChunk004.row5109_mem, Shared.BasisChunk004.row5110_mem, Shared.BasisChunk004.row5111_mem, Shared.BasisChunk004.row5114_mem, Shared.BasisChunk004.row5115_mem, Shared.BasisChunk004.row5116_mem, Shared.BasisChunk004.row5117_mem, Shared.BasisChunk004.row5118_mem, Shared.BasisChunk004.row5119_mem, Shared.BasisChunk005.row5120_mem, Shared.BasisChunk005.row5121_mem, Shared.BasisChunk005.row5124_mem, Shared.BasisChunk005.row5125_mem, Shared.BasisChunk005.row5126_mem, Shared.BasisChunk005.row5127_mem, Shared.BasisChunk005.row5128_mem, Shared.BasisChunk005.row5129_mem, Shared.BasisChunk005.row5130_mem, Shared.BasisChunk005.row5132_mem, Shared.BasisChunk005.row5133_mem, Shared.BasisChunk005.row5134_mem, Shared.BasisChunk005.row5135_mem, Shared.BasisChunk005.row5136_mem, Shared.BasisChunk005.row5137_mem, Shared.BasisChunk005.row5138_mem, Shared.BasisChunk005.row5140_mem, Shared.BasisChunk005.row5141_mem, Shared.BasisChunk005.row5142_mem, Shared.BasisChunk005.row5143_mem, Shared.BasisChunk005.row5144_mem, Shared.BasisChunk005.row5145_mem, Shared.BasisChunk005.row5146_mem, Shared.BasisChunk005.row5147_mem, Shared.BasisChunk005.row5148_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard066
