import KIP126.LinProgram.Generated.Naturality.Words200.Shard119
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk051
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk052
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard119
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard119
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
  exact ⟨Shared.RelationChunk002.relation244_zero, Shared.RelationChunk030.relation1269_zero, Shared.RelationChunk051.relation1817_zero, Shared.RelationChunk051.relation1818_zero, Shared.RelationChunk052.relation1820_zero, Shared.RelationChunk052.relation1821_zero, Shared.RelationChunk052.relation1822_zero, Shared.RelationChunk052.relation1823_zero, Shared.RelationChunk052.relation1824_zero, Shared.RelationChunk052.relation1825_zero, Shared.RelationChunk052.relation1826_zero, Shared.RelationChunk052.relation1827_zero, Shared.RelationChunk052.relation1828_zero, Shared.RelationChunk052.relation1829_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15234 128 := by cbv
private def targetRows : List BasisRow := [⟨34, 196, 0, "1102,1"⟩,
  ⟨33, 196, 0, "8,1,863,1"⟩,
  ⟨32, 196, 0, "8,2,642,1"⟩,
  ⟨31, 196, 0, "8,1,864,1"⟩,
  ⟨30, 196, 0, "13,1,784,1"⟩,
  ⟨30, 196, 2, "0,2,64,1,347,1"⟩,
  ⟨30, 196, 3, "0,2,8,2,627,1"⟩,
  ⟨29, 196, 0, "1103,1"⟩,
  ⟨29, 196, 1, "13,2,537,1"⟩,
  ⟨29, 196, 2, "13,5,105,1"⟩,
  ⟨29, 196, 4, "0,2,138,1,209,1"⟩,
  ⟨29, 196, 5, "0,2,8,1,832,1"⟩,
  ⟨28, 196, 0, "9,1,13,3,23,1,75,1"⟩,
  ⟨28, 196, 1, "0,2,1078,1"⟩,
  ⟨28, 196, 2, "0,2,23,1,627,1"⟩,
  ⟨27, 196, 0, "0,2,1079,1"⟩,
  ⟨27, 196, 1, "0,2,64,1,349,1"⟩,
  ⟨26, 196, 1, "0,2,1081,1"⟩,
  ⟨26, 196, 2, "0,3,1063,1"⟩,
  ⟨25, 196, 1, "0,2,1082,1"⟩,
  ⟨25, 196, 2, "0,4,1051,1"⟩,
  ⟨24, 196, 0, "1104,1"⟩,
  ⟨24, 196, 2, "0,2,1084,1"⟩,
  ⟨24, 196, 3, "0,2,1083,1"⟩,
  ⟨23, 196, 0, "1105,1"⟩,
  ⟨23, 196, 2, "13,1,23,1,417,1"⟩,
  ⟨23, 196, 3, "1,1,1083,1"⟩,
  ⟨23, 196, 4, "0,2,71,1,324,1"⟩,
  ⟨23, 196, 5, "0,3,1064,1"⟩,
  ⟨22, 196, 0, "68,1,359,1"⟩,
  ⟨22, 196, 1, "9,1,75,1,212,1"⟩,
  ⟨22, 196, 3, "1,1,64,1,351,1"⟩,
  ⟨22, 196, 4, "1,1,3,1,959,1"⟩,
  ⟨22, 196, 5, "0,8,59,1,324,1"⟩,
  ⟨21, 196, 1, "18,1,690,1"⟩,
  ⟨21, 196, 2, "3,1,982,1"⟩,
  ⟨21, 196, 3, "0,3,1068,1"⟩,
  ⟨20, 196, 0, "1108,1"⟩,
  ⟨20, 196, 2, "9,1,13,1,569,1"⟩,
  ⟨20, 196, 3, "3,1,984,1"⟩,
  ⟨20, 196, 4, "2,1,1052,1"⟩,
  ⟨19, 196, 0, "1109,1"⟩,
  ⟨19, 196, 1, "67,1,363,1"⟩,
  ⟨19, 196, 3, "0,1,1096,1"⟩,
  ⟨19, 196, 4, "0,2,8,2,16,1,324,1"⟩,
  ⟨18, 196, 0, "1110,1"⟩,
  ⟨18, 196, 1, "0,1,1097,1"⟩,
  ⟨18, 196, 2, "0,1,3,1,965,1"⟩,
  ⟨18, 196, 3, "0,2,8,2,17,1,324,1"⟩,
  ⟨18, 196, 4, "0,4,1055,1"⟩,
  ⟨17, 196, 0, "1111,1"⟩,
  ⟨17, 196, 1, "13,1,787,1"⟩,
  ⟨17, 196, 2, "2,1,1054,1"⟩,
  ⟨17, 196, 3, "1,1,1087,1"⟩,
  ⟨17, 196, 4, "0,2,1088,1"⟩,
  ⟨17, 196, 5, "0,4,1057,1"⟩,
  ⟨16, 196, 0, "1113,1"⟩,
  ⟨16, 196, 4, "1,2,1055,1"⟩,
  ⟨16, 196, 6, "0,5,64,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row9024_mem, Shared.BasisChunk008.row9025_mem, Shared.BasisChunk008.row9027_mem, Shared.BasisChunk008.row9028_mem, Shared.BasisChunk008.row9029_mem, Shared.BasisChunk008.row9031_mem, Shared.BasisChunk008.row9032_mem, Shared.BasisChunk008.row9033_mem, Shared.BasisChunk008.row9034_mem, Shared.BasisChunk008.row9035_mem, Shared.BasisChunk008.row9037_mem, Shared.BasisChunk008.row9038_mem, Shared.BasisChunk008.row9039_mem, Shared.BasisChunk008.row9040_mem, Shared.BasisChunk008.row9041_mem, Shared.BasisChunk008.row9042_mem, Shared.BasisChunk008.row9043_mem, Shared.BasisChunk008.row9045_mem, Shared.BasisChunk008.row9046_mem, Shared.BasisChunk008.row9048_mem, Shared.BasisChunk008.row9049_mem, Shared.BasisChunk008.row9050_mem, Shared.BasisChunk008.row9052_mem, Shared.BasisChunk008.row9053_mem, Shared.BasisChunk008.row9054_mem, Shared.BasisChunk008.row9056_mem, Shared.BasisChunk008.row9057_mem, Shared.BasisChunk008.row9058_mem, Shared.BasisChunk008.row9059_mem, Shared.BasisChunk008.row9060_mem, Shared.BasisChunk008.row9061_mem, Shared.BasisChunk008.row9063_mem, Shared.BasisChunk008.row9064_mem, Shared.BasisChunk008.row9065_mem, Shared.BasisChunk008.row9067_mem, Shared.BasisChunk008.row9068_mem, Shared.BasisChunk008.row9069_mem, Shared.BasisChunk008.row9070_mem, Shared.BasisChunk008.row9072_mem, Shared.BasisChunk008.row9073_mem, Shared.BasisChunk008.row9074_mem, Shared.BasisChunk008.row9075_mem, Shared.BasisChunk008.row9076_mem, Shared.BasisChunk008.row9078_mem, Shared.BasisChunk008.row9079_mem, Shared.BasisChunk008.row9080_mem, Shared.BasisChunk008.row9081_mem, Shared.BasisChunk008.row9082_mem, Shared.BasisChunk008.row9083_mem, Shared.BasisChunk008.row9084_mem, Shared.BasisChunk008.row9085_mem, Shared.BasisChunk008.row9086_mem, Shared.BasisChunk008.row9087_mem, Shared.BasisChunk008.row9088_mem, Shared.BasisChunk008.row9089_mem, Shared.BasisChunk008.row9090_mem, Shared.BasisChunk008.row9091_mem, Shared.BasisChunk008.row9095_mem, Shared.BasisChunk008.row9097_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard119
