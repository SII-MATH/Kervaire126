module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard013
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard013
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
  exact ⟨Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation128_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, Shared.RelationChunk001.relation203_zero, Shared.RelationChunk001.relation204_zero, Shared.RelationChunk001.relation205_zero, Shared.RelationChunk001.relation206_zero, Shared.RelationChunk001.relation209_zero, Shared.RelationChunk001.relation210_zero, Shared.RelationChunk002.relation212_zero, Shared.RelationChunk002.relation213_zero, Shared.RelationChunk002.relation218_zero, Shared.RelationChunk002.relation220_zero, Shared.RelationChunk002.relation221_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1666 128 := by cbv
private def targetRows : List BasisRow := [⟨15, 91, 0, "0,1,8,1,89,1"⟩,
  ⟨14, 91, 0, "0,1,9,1,80,1"⟩,
  ⟨14, 91, 1, "0,7,128,1"⟩,
  ⟨13, 91, 0, "1,1,144,1"⟩,
  ⟨13, 91, 1, "0,3,141,1"⟩,
  ⟨10, 91, 0, "13,1,75,1"⟩,
  ⟨10, 91, 1, "0,1,3,1,120,1"⟩,
  ⟨7, 91, 0, "0,3,142,1"⟩,
  ⟨6, 91, 1, "0,3,143,1"⟩,
  ⟨92, 92, 0, "0,92"⟩,
  ⟨30, 92, 0, "0,2,145,1"⟩,
  ⟨29, 92, 1, "0,28,69,1"⟩,
  ⟨26, 92, 0, "0,2,8,2,49,1"⟩,
  ⟨25, 92, 0, "0,2,8,2,50,1"⟩,
  ⟨23, 92, 0, "0,5,137,1"⟩,
  ⟨22, 92, 0, "0,5,138,1"⟩,
  ⟨20, 92, 0, "0,2,146,1"⟩,
  ⟨19, 92, 0, "0,2,147,1"⟩,
  ⟨15, 92, 0, "0,2,9,1,80,1"⟩,
  ⟨13, 92, 0, "150,1"⟩,
  ⟨11, 92, 1, "0,1,13,1,75,1"⟩,
  ⟨10, 92, 0, "15,1,69,1"⟩,
  ⟨8, 92, 0, "0,4,142,1"⟩,
  ⟨7, 92, 0, "0,4,143,1"⟩,
  ⟨6, 92, 0, "2,1,13,1,69,1"⟩,
  ⟨6, 92, 1, "1,2,142,1"⟩,
  ⟨5, 92, 0, "1,2,143,1"⟩,
  ⟨93, 93, 0, "0,93"⟩,
  ⟨30, 93, 0, "0,29,69,1"⟩,
  ⟨27, 93, 0, "153,1"⟩,
  ⟨24, 93, 1, "0,6,137,1"⟩,
  ⟨23, 93, 0, "8,2,56,1"⟩,
  ⟨23, 93, 1, "0,6,138,1"⟩,
  ⟨22, 93, 0, "8,1,17,1,40,1"⟩,
  ⟨21, 93, 0, "8,1,100,1"⟩,
  ⟨21, 93, 1, "0,3,146,1"⟩,
  ⟨20, 93, 0, "8,4,9,1"⟩,
  ⟨19, 93, 0, "8,3,29,1"⟩,
  ⟨18, 93, 1, "8,2,9,1,23,1"⟩,
  ⟨17, 93, 0, "17,1,64,1"⟩,
  ⟨17, 93, 1, "8,1,9,1,51,1"⟩,
  ⟨17, 93, 2, "0,1,149,1"⟩,
  ⟨16, 93, 0, "154,1"⟩,
  ⟨16, 93, 1, "9,1,13,3"⟩,
  ⟨13, 93, 0, "13,1,80,1"⟩,
  ⟨12, 93, 0, "155,1"⟩,
  ⟨11, 93, 0, "0,1,15,1,69,1"⟩,
  ⟨10, 93, 0, "1,1,13,1,76,1"⟩,
  ⟨9, 93, 0, "2,1,7,1,95,1"⟩,
  ⟨8, 93, 0, "0,5,143,1"⟩,
  ⟨7, 93, 0, "1,1,148,1"⟩,
  ⟨7, 93, 1, "0,1,2,1,13,1,69,1"⟩,
  ⟨6, 93, 0, "1,1,4,1,7,1,69,1"⟩,
  ⟨94, 94, 0, "0,94"⟩,
  ⟨31, 94, 0, "0,30,69,1"⟩,
  ⟨29, 94, 0, "0,1,152,1"⟩,
  ⟨28, 94, 0, "0,1,153,1"⟩,
  ⟨25, 94, 0, "0,7,137,1"⟩,
  ⟨24, 94, 0, "0,7,138,1"⟩,
  ⟨19, 94, 0, "0,1,16,1,64,1"⟩,
  ⟨18, 94, 0, "0,1,17,1,64,1"⟩,
  ⟨18, 94, 1, "0,2,149,1"⟩,
  ⟨17, 94, 1, "0,1,154,1"⟩,
  ⟨15, 94, 0, "0,1,8,1,101,1"⟩,
  ⟨14, 94, 1, "0,1,13,1,80,1"⟩,
  ⟨13, 94, 0, "0,1,155,1"⟩,
  ⟨12, 94, 0, "13,1,83,1"⟩,
  ⟨12, 94, 1, "0,2,15,1,69,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row1004_mem, Shared.BasisChunk000.row1005_mem, Shared.BasisChunk000.row1006_mem, Shared.BasisChunk000.row1007_mem, Shared.BasisChunk000.row1008_mem, Shared.BasisChunk000.row1009_mem, Shared.BasisChunk000.row1010_mem, Shared.BasisChunk000.row1012_mem, Shared.BasisChunk000.row1014_mem, Shared.BasisChunk000.row1016_mem, Shared.BasisChunk000.row1017_mem, Shared.BasisChunk000.row1019_mem, Shared.BasisChunk000.row1020_mem, Shared.BasisChunk000.row1021_mem, Shared.BasisChunk000.row1022_mem, Shared.BasisChunk000.row1023_mem, Shared.BasisChunk001.row1024_mem, Shared.BasisChunk001.row1025_mem, Shared.BasisChunk001.row1027_mem, Shared.BasisChunk001.row1028_mem, Shared.BasisChunk001.row1031_mem, Shared.BasisChunk001.row1032_mem, Shared.BasisChunk001.row1033_mem, Shared.BasisChunk001.row1034_mem, Shared.BasisChunk001.row1035_mem, Shared.BasisChunk001.row1036_mem, Shared.BasisChunk001.row1037_mem, Shared.BasisChunk001.row1038_mem, Shared.BasisChunk001.row1039_mem, Shared.BasisChunk001.row1041_mem, Shared.BasisChunk001.row1043_mem, Shared.BasisChunk001.row1044_mem, Shared.BasisChunk001.row1045_mem, Shared.BasisChunk001.row1046_mem, Shared.BasisChunk001.row1047_mem, Shared.BasisChunk001.row1048_mem, Shared.BasisChunk001.row1049_mem, Shared.BasisChunk001.row1050_mem, Shared.BasisChunk001.row1052_mem, Shared.BasisChunk001.row1053_mem, Shared.BasisChunk001.row1054_mem, Shared.BasisChunk001.row1055_mem, Shared.BasisChunk001.row1056_mem, Shared.BasisChunk001.row1057_mem, Shared.BasisChunk001.row1059_mem, Shared.BasisChunk001.row1060_mem, Shared.BasisChunk001.row1061_mem, Shared.BasisChunk001.row1062_mem, Shared.BasisChunk001.row1063_mem, Shared.BasisChunk001.row1064_mem, Shared.BasisChunk001.row1065_mem, Shared.BasisChunk001.row1066_mem, Shared.BasisChunk001.row1067_mem, Shared.BasisChunk001.row1068_mem, Shared.BasisChunk001.row1069_mem, Shared.BasisChunk001.row1071_mem, Shared.BasisChunk001.row1072_mem, Shared.BasisChunk001.row1073_mem, Shared.BasisChunk001.row1074_mem, Shared.BasisChunk001.row1075_mem, Shared.BasisChunk001.row1076_mem, Shared.BasisChunk001.row1077_mem, Shared.BasisChunk001.row1079_mem, Shared.BasisChunk001.row1080_mem, Shared.BasisChunk001.row1082_mem, Shared.BasisChunk001.row1083_mem, Shared.BasisChunk001.row1084_mem, Shared.BasisChunk001.row1085_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard013
