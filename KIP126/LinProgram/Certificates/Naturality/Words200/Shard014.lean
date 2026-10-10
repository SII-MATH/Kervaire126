import KIP126.LinProgram.Generated.Naturality.Words200.Shard014
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard014
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard014
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
  exact ⟨Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk002.relation224_zero, Shared.RelationChunk002.relation225_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation228_zero, Shared.RelationChunk002.relation232_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1794 128 := by cbv
private def targetRows : List BasisRow := [⟨11, 94, 0, "9,1,95,1"⟩,
  ⟨8, 94, 0, "17,1,69,1"⟩,
  ⟨95, 95, 0, "0,95"⟩,
  ⟨32, 95, 0, "0,31,69,1"⟩,
  ⟨30, 95, 0, "0,2,152,1"⟩,
  ⟨29, 95, 0, "0,2,153,1"⟩,
  ⟨26, 95, 0, "0,8,137,1"⟩,
  ⟨25, 95, 0, "0,8,138,1"⟩,
  ⟨20, 95, 0, "0,2,16,1,64,1"⟩,
  ⟨19, 95, 0, "0,2,17,1,64,1"⟩,
  ⟨19, 95, 1, "0,3,149,1"⟩,
  ⟨18, 95, 0, "0,2,154,1"⟩,
  ⟨15, 95, 0, "0,2,13,1,80,1"⟩,
  ⟨10, 95, 0, "0,1,16,1,69,1"⟩,
  ⟨9, 95, 0, "0,1,17,1,69,1"⟩,
  ⟨96, 96, 0, "0,96"⟩,
  ⟨31, 96, 0, "0,3,152,1"⟩,
  ⟨27, 96, 0, "8,1,111,1"⟩,
  ⟨24, 96, 0, "8,3,31,1"⟩,
  ⟨23, 96, 0, "8,2,16,1,17,1"⟩,
  ⟨22, 96, 0, "8,2,17,2"⟩,
  ⟨21, 96, 0, "8,2,60,1"⟩,
  ⟨20, 96, 0, "8,4,13,1"⟩,
  ⟨20, 96, 1, "0,4,149,1"⟩,
  ⟨19, 96, 0, "8,3,32,1"⟩,
  ⟨19, 96, 1, "0,3,154,1"⟩,
  ⟨18, 96, 1, "8,2,13,1,23,1"⟩,
  ⟨17, 96, 0, "8,1,113,1"⟩,
  ⟨17, 96, 1, "8,1,13,1,51,1"⟩,
  ⟨17, 96, 2, "0,1,160,1"⟩,
  ⟨16, 96, 0, "162,1"⟩,
  ⟨16, 96, 1, "13,4"⟩,
  ⟨15, 96, 0, "13,1,23,1,24,1"⟩,
  ⟨15, 96, 1, "1,1,156,1"⟩,
  ⟨14, 96, 0, "9,1,101,1"⟩,
  ⟨14, 96, 1, "2,1,150,1"⟩,
  ⟨13, 96, 0, "2,1,151,1"⟩,
  ⟨11, 96, 0, "1,1,157,1"⟩,
  ⟨11, 96, 1, "0,2,16,1,69,1"⟩,
  ⟨10, 96, 1, "0,2,17,1,69,1"⟩,
  ⟨9, 96, 0, "7,2,67,1"⟩,
  ⟨8, 96, 0, "7,2,68,1"⟩,
  ⟨8, 96, 1, "1,1,158,1"⟩,
  ⟨7, 96, 0, "2,2,13,1,69,1"⟩,
  ⟨97, 97, 0, "0,97"⟩,
  ⟨32, 97, 0, "1,1,159,1"⟩,
  ⟨29, 97, 0, "0,1,8,1,110,1"⟩,
  ⟨28, 97, 0, "0,1,8,1,111,1"⟩,
  ⟨21, 97, 0, "0,5,149,1"⟩,
  ⟨20, 97, 0, "0,4,154,1"⟩,
  ⟨19, 97, 0, "0,1,8,1,112,1"⟩,
  ⟨18, 97, 0, "0,1,8,1,113,1"⟩,
  ⟨18, 97, 1, "0,2,160,1"⟩,
  ⟨17, 97, 0, "0,1,162,1"⟩,
  ⟨11, 97, 0, "13,1,95,1"⟩,
  ⟨11, 97, 1, "0,3,17,1,69,1"⟩,
  ⟨10, 97, 0, "164,1"⟩,
  ⟨9, 97, 1, "0,1,7,2,68,1"⟩,
  ⟨8, 97, 0, "20,1,69,1"⟩,
  ⟨5, 97, 0, "0,1,163,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1086_mem, Shared.BasisChunk001.row1089_mem, Shared.BasisChunk001.row1091_mem, Shared.BasisChunk001.row1092_mem, Shared.BasisChunk001.row1094_mem, Shared.BasisChunk001.row1095_mem, Shared.BasisChunk001.row1096_mem, Shared.BasisChunk001.row1097_mem, Shared.BasisChunk001.row1098_mem, Shared.BasisChunk001.row1099_mem, Shared.BasisChunk001.row1100_mem, Shared.BasisChunk001.row1101_mem, Shared.BasisChunk001.row1103_mem, Shared.BasisChunk001.row1104_mem, Shared.BasisChunk001.row1105_mem, Shared.BasisChunk001.row1106_mem, Shared.BasisChunk001.row1107_mem, Shared.BasisChunk001.row1109_mem, Shared.BasisChunk001.row1111_mem, Shared.BasisChunk001.row1112_mem, Shared.BasisChunk001.row1113_mem, Shared.BasisChunk001.row1114_mem, Shared.BasisChunk001.row1115_mem, Shared.BasisChunk001.row1116_mem, Shared.BasisChunk001.row1117_mem, Shared.BasisChunk001.row1118_mem, Shared.BasisChunk001.row1120_mem, Shared.BasisChunk001.row1122_mem, Shared.BasisChunk001.row1123_mem, Shared.BasisChunk001.row1124_mem, Shared.BasisChunk001.row1125_mem, Shared.BasisChunk001.row1126_mem, Shared.BasisChunk001.row1127_mem, Shared.BasisChunk001.row1128_mem, Shared.BasisChunk001.row1129_mem, Shared.BasisChunk001.row1130_mem, Shared.BasisChunk001.row1131_mem, Shared.BasisChunk001.row1132_mem, Shared.BasisChunk001.row1133_mem, Shared.BasisChunk001.row1135_mem, Shared.BasisChunk001.row1136_mem, Shared.BasisChunk001.row1137_mem, Shared.BasisChunk001.row1138_mem, Shared.BasisChunk001.row1139_mem, Shared.BasisChunk001.row1142_mem, Shared.BasisChunk001.row1143_mem, Shared.BasisChunk001.row1144_mem, Shared.BasisChunk001.row1145_mem, Shared.BasisChunk001.row1146_mem, Shared.BasisChunk001.row1147_mem, Shared.BasisChunk001.row1148_mem, Shared.BasisChunk001.row1149_mem, Shared.BasisChunk001.row1150_mem, Shared.BasisChunk001.row1151_mem, Shared.BasisChunk001.row1152_mem, Shared.BasisChunk001.row1153_mem, Shared.BasisChunk001.row1154_mem, Shared.BasisChunk001.row1156_mem, Shared.BasisChunk001.row1157_mem, Shared.BasisChunk001.row1159_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard014
