module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard078
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk027
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard078
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard078
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation36_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation67_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation74_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation150_zero, Shared.RelationChunk001.relation154_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk002.relation239_zero, Shared.RelationChunk002.relation240_zero, Shared.RelationChunk002.relation241_zero, Shared.RelationChunk003.relation265_zero, Shared.RelationChunk003.relation266_zero, Shared.RelationChunk003.relation267_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation326_zero, Shared.RelationChunk005.relation327_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk005.relation331_zero, Shared.RelationChunk005.relation332_zero, Shared.RelationChunk005.relation333_zero, Shared.RelationChunk006.relation364_zero, Shared.RelationChunk009.relation485_zero, Shared.RelationChunk009.relation489_zero, Shared.RelationChunk009.relation495_zero, Shared.RelationChunk011.relation584_zero, Shared.RelationChunk013.relation678_zero, Shared.RelationChunk015.relation777_zero, Shared.RelationChunk016.relation790_zero, Shared.RelationChunk016.relation793_zero, Shared.RelationChunk016.relation794_zero, Shared.RelationChunk016.relation795_zero, Shared.RelationChunk016.relation797_zero, Shared.RelationChunk025.relation1096_zero, Shared.RelationChunk025.relation1097_zero, Shared.RelationChunk025.relation1100_zero, Shared.RelationChunk025.relation1101_zero, Shared.RelationChunk025.relation1109_zero, Shared.RelationChunk026.relation1111_zero, Shared.RelationChunk026.relation1124_zero, Shared.RelationChunk026.relation1134_zero, Shared.RelationChunk026.relation1135_zero, Shared.RelationChunk026.relation1136_zero, Shared.RelationChunk026.relation1137_zero, Shared.RelationChunk026.relation1138_zero, Shared.RelationChunk026.relation1139_zero, Shared.RelationChunk026.relation1140_zero, Shared.RelationChunk027.relation1142_zero, Shared.RelationChunk027.relation1143_zero, Shared.RelationChunk027.relation1144_zero, Shared.RelationChunk027.relation1145_zero, Shared.RelationChunk027.relation1146_zero, Shared.RelationChunk027.relation1147_zero, Shared.RelationChunk027.relation1148_zero, Shared.RelationChunk027.relation1149_zero, Shared.RelationChunk027.relation1150_zero, Shared.RelationChunk027.relation1151_zero, Shared.RelationChunk027.relation1152_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9986 128 := by cbv
private def targetRows : List BasisRow := [⟨43, 171, 0, "8,5,117,1"⟩,
  ⟨42, 171, 1, "8,4,17,1,78,1"⟩,
  ⟨41, 171, 0, "8,2,403,1"⟩,
  ⟨41, 171, 1, "8,4,171,1"⟩,
  ⟨41, 171, 2, "0,1,16,1,452,1"⟩,
  ⟨40, 171, 0, "16,1,17,1,225,1"⟩,
  ⟨40, 171, 1, "8,7,39,1"⟩,
  ⟨40, 171, 2, "0,1,17,1,452,1"⟩,
  ⟨39, 171, 1, "17,2,225,1"⟩,
  ⟨39, 171, 2, "8,7,40,1"⟩,
  ⟨38, 171, 0, "8,3,16,1,137,1"⟩,
  ⟨38, 171, 1, "8,6,17,1,20,1"⟩,
  ⟨38, 171, 2, "0,4,725,1"⟩,
  ⟨37, 171, 0, "8,3,16,1,138,1"⟩,
  ⟨37, 171, 1, "8,6,63,1"⟩,
  ⟨37, 171, 2, "0,2,752,1"⟩,
  ⟨36, 171, 0, "8,3,17,1,138,1"⟩,
  ⟨36, 171, 1, "8,7,9,1,13,1"⟩,
  ⟨35, 171, 0, "8,2,42,1,137,1"⟩,
  ⟨35, 171, 1, "8,6,9,1,32,1"⟩,
  ⟨35, 171, 2, "0,1,759,1"⟩,
  ⟨34, 171, 0, "778,1"⟩,
  ⟨34, 171, 1, "8,5,9,1,13,1,23,1"⟩,
  ⟨34, 171, 2, "8,6,64,1"⟩,
  ⟨33, 171, 0, "8,4,9,1,13,1,51,1"⟩,
  ⟨33, 171, 1, "8,5,118,1"⟩,
  ⟨32, 171, 0, "8,1,64,1,146,1"⟩,
  ⟨32, 171, 1, "8,3,9,1,13,4"⟩,
  ⟨32, 171, 2, "8,4,17,1,80,1"⟩,
  ⟨32, 171, 3, "1,1,5,1,64,1,149,1"⟩,
  ⟨31, 171, 0, "8,1,64,1,147,1"⟩,
  ⟨31, 171, 1, "8,2,9,1,13,3,32,1"⟩,
  ⟨31, 171, 2, "8,4,173,1"⟩,
  ⟨31, 171, 3, "0,1,8,2,380,1"⟩,
  ⟨30, 171, 0, "8,1,9,1,13,4,23,1"⟩,
  ⟨30, 171, 1, "8,2,404,1"⟩,
  ⟨30, 171, 2, "8,4,13,1,101,1"⟩,
  ⟨30, 171, 3, "0,1,8,1,17,1,278,1"⟩,
  ⟨29, 171, 0, "9,1,13,4,51,1"⟩,
  ⟨29, 171, 1, "8,1,580,1"⟩,
  ⟨29, 171, 2, "8,3,13,2,80,1"⟩,
  ⟨29, 171, 3, "0,1,17,1,454,1"⟩,
  ⟨28, 171, 0, "8,2,13,1,23,1,101,1"⟩,
  ⟨28, 171, 1, "8,3,254,1"⟩,
  ⟨28, 171, 2, "0,6,64,1,187,1"⟩,
  ⟨27, 171, 0, "8,1,13,2,23,1,80,1"⟩,
  ⟨27, 171, 1, "8,3,255,1"⟩,
  ⟨27, 171, 2, "0,6,64,1,188,1"⟩,
  ⟨26, 171, 0, "13,4,101,1"⟩,
  ⟨26, 171, 1, "8,2,20,1,188,1"⟩,
  ⟨25, 171, 0, "8,1,20,1,267,1"⟩,
  ⟨25, 171, 1, "0,6,706,1"⟩,
  ⟨24, 171, 0, "8,1,9,1,13,1,212,1"⟩,
  ⟨24, 171, 1, "0,2,8,1,69,1,138,1"⟩,
  ⟨23, 171, 1, "9,1,13,2,188,1"⟩,
  ⟨22, 171, 0, "64,1,212,1"⟩,
  ⟨22, 171, 1, "13,2,286,1"⟩,
  ⟨21, 171, 0, "79,1,188,1"⟩,
  ⟨21, 171, 1, "13,2,287,1"⟩,
  ⟨21, 171, 3, "0,1,64,1,209,1"⟩,
  ⟨20, 171, 0, "80,1,188,1"⟩,
  ⟨20, 171, 1, "17,1,475,1"⟩,
  ⟨20, 171, 2, "0,1,760,1"⟩,
  ⟨19, 171, 0, "780,1"⟩,
  ⟨18, 171, 0, "43,1,285,1"⟩,
  ⟨18, 171, 1, "13,2,288,1"⟩,
  ⟨18, 171, 2, "3,2,604,1"⟩,
  ⟨18, 171, 3, "0,1,762,1"⟩,
  ⟨17, 171, 0, "43,1,287,1"⟩,
  ⟨17, 171, 1, "13,1,532,1"⟩,
  ⟨17, 171, 2, "8,2,414,1"⟩,
  ⟨17, 171, 3, "0,1,763,1"⟩,
  ⟨17, 171, 4, "0,1,3,1,669,1"⟩,
  ⟨17, 171, 5, "0,9,676,1"⟩,
  ⟨16, 171, 1, "8,2,415,1"⟩,
  ⟨16, 171, 2, "1,1,76,1,189,1"⟩,
  ⟨16, 171, 3, "0,1,765,1"⟩,
  ⟨16, 171, 4, "0,1,764,1"⟩,
  ⟨16, 171, 5, "0,4,732,1"⟩,
  ⟨15, 171, 0, "8,1,583,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5982_mem, Shared.BasisChunk005.row5984_mem, Shared.BasisChunk005.row5985_mem, Shared.BasisChunk005.row5986_mem, Shared.BasisChunk005.row5987_mem, Shared.BasisChunk005.row5988_mem, Shared.BasisChunk005.row5989_mem, Shared.BasisChunk005.row5990_mem, Shared.BasisChunk005.row5992_mem, Shared.BasisChunk005.row5993_mem, Shared.BasisChunk005.row5994_mem, Shared.BasisChunk005.row5995_mem, Shared.BasisChunk005.row5996_mem, Shared.BasisChunk005.row5997_mem, Shared.BasisChunk005.row5998_mem, Shared.BasisChunk005.row5999_mem, Shared.BasisChunk005.row6000_mem, Shared.BasisChunk005.row6001_mem, Shared.BasisChunk005.row6003_mem, Shared.BasisChunk005.row6004_mem, Shared.BasisChunk005.row6005_mem, Shared.BasisChunk005.row6006_mem, Shared.BasisChunk005.row6007_mem, Shared.BasisChunk005.row6008_mem, Shared.BasisChunk005.row6009_mem, Shared.BasisChunk005.row6010_mem, Shared.BasisChunk005.row6011_mem, Shared.BasisChunk005.row6012_mem, Shared.BasisChunk005.row6013_mem, Shared.BasisChunk005.row6014_mem, Shared.BasisChunk005.row6015_mem, Shared.BasisChunk005.row6016_mem, Shared.BasisChunk005.row6017_mem, Shared.BasisChunk005.row6018_mem, Shared.BasisChunk005.row6019_mem, Shared.BasisChunk005.row6020_mem, Shared.BasisChunk005.row6021_mem, Shared.BasisChunk005.row6022_mem, Shared.BasisChunk005.row6023_mem, Shared.BasisChunk005.row6024_mem, Shared.BasisChunk005.row6025_mem, Shared.BasisChunk005.row6026_mem, Shared.BasisChunk005.row6027_mem, Shared.BasisChunk005.row6028_mem, Shared.BasisChunk005.row6029_mem, Shared.BasisChunk005.row6030_mem, Shared.BasisChunk005.row6031_mem, Shared.BasisChunk005.row6032_mem, Shared.BasisChunk005.row6033_mem, Shared.BasisChunk005.row6034_mem, Shared.BasisChunk005.row6035_mem, Shared.BasisChunk005.row6036_mem, Shared.BasisChunk005.row6037_mem, Shared.BasisChunk005.row6038_mem, Shared.BasisChunk005.row6040_mem, Shared.BasisChunk005.row6041_mem, Shared.BasisChunk005.row6042_mem, Shared.BasisChunk005.row6043_mem, Shared.BasisChunk005.row6044_mem, Shared.BasisChunk005.row6046_mem, Shared.BasisChunk005.row6047_mem, Shared.BasisChunk005.row6048_mem, Shared.BasisChunk005.row6049_mem, Shared.BasisChunk005.row6050_mem, Shared.BasisChunk005.row6051_mem, Shared.BasisChunk005.row6052_mem, Shared.BasisChunk005.row6053_mem, Shared.BasisChunk005.row6054_mem, Shared.BasisChunk005.row6055_mem, Shared.BasisChunk005.row6056_mem, Shared.BasisChunk005.row6057_mem, Shared.BasisChunk005.row6058_mem, Shared.BasisChunk005.row6059_mem, Shared.BasisChunk005.row6060_mem, Shared.BasisChunk005.row6062_mem, Shared.BasisChunk005.row6063_mem, Shared.BasisChunk005.row6064_mem, Shared.BasisChunk005.row6065_mem, Shared.BasisChunk005.row6066_mem, Shared.BasisChunk005.row6067_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard078
