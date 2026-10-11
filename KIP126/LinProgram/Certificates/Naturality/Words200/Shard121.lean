module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard121
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk033
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk049
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk050
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk053
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk009

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard121
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard121
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk001.relation189_zero, Shared.RelationChunk008.relation473_zero, Shared.RelationChunk011.relation604_zero, Shared.RelationChunk011.relation605_zero, Shared.RelationChunk020.relation917_zero, Shared.RelationChunk020.relation918_zero, Shared.RelationChunk020.relation920_zero, Shared.RelationChunk020.relation921_zero, Shared.RelationChunk020.relation922_zero, Shared.RelationChunk020.relation923_zero, Shared.RelationChunk020.relation924_zero, Shared.RelationChunk028.relation1180_zero, Shared.RelationChunk028.relation1181_zero, Shared.RelationChunk033.relation1381_zero, Shared.RelationChunk034.relation1382_zero, Shared.RelationChunk034.relation1383_zero, Shared.RelationChunk034.relation1384_zero, Shared.RelationChunk049.relation1772_zero, Shared.RelationChunk050.relation1797_zero, Shared.RelationChunk053.relation1832_zero, Shared.RelationChunk053.relation1833_zero, Shared.RelationChunk053.relation1834_zero, Shared.RelationChunk053.relation1835_zero, Shared.RelationChunk053.relation1836_zero, Shared.RelationChunk053.relation1837_zero, Shared.RelationChunk053.relation1838_zero, Shared.RelationChunk053.relation1839_zero, Shared.RelationChunk053.relation1840_zero, Shared.RelationChunk053.relation1841_zero, Shared.RelationChunk053.relation1845_zero, Shared.RelationChunk053.relation1848_zero, Shared.RelationChunk053.relation1849_zero, Shared.RelationChunk053.relation1850_zero, Shared.RelationChunk053.relation1852_zero, Shared.RelationChunk053.relation1853_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15490 128 := by cbv
private def targetRows : List BasisRow := [⟨31, 197, 0, "113,1,260,1"⟩,
  ⟨31, 197, 1, "8,2,23,1,292,1"⟩,
  ⟨31, 197, 2, "8,4,293,1"⟩,
  ⟨31, 197, 3, "0,3,64,1,347,1"⟩,
  ⟨30, 197, 0, "8,1,13,2,346,1"⟩,
  ⟨30, 197, 1, "8,5,209,1"⟩,
  ⟨30, 197, 2, "0,1,1103,1"⟩,
  ⟨30, 197, 3, "0,3,138,1,209,1"⟩,
  ⟨29, 197, 0, "13,3,292,1"⟩,
  ⟨29, 197, 1, "8,4,294,1"⟩,
  ⟨29, 197, 2, "1,1,1095,1"⟩,
  ⟨29, 197, 3, "0,3,23,1,627,1"⟩,
  ⟨28, 197, 2, "8,3,13,1,261,1"⟩,
  ⟨28, 197, 3, "0,3,1079,1"⟩,
  ⟨28, 197, 4, "0,3,64,1,349,1"⟩,
  ⟨27, 197, 0, "64,1,383,1"⟩,
  ⟨27, 197, 1, "8,1,874,1"⟩,
  ⟨27, 197, 2, "8,2,13,1,423,1"⟩,
  ⟨27, 197, 3, "0,3,1081,1"⟩,
  ⟨27, 197, 4, "0,4,1063,1"⟩,
  ⟨26, 197, 0, "23,1,655,1"⟩,
  ⟨26, 197, 1, "8,1,64,1,250,1"⟩,
  ⟨26, 197, 2, "8,1,13,3,209,1"⟩,
  ⟨26, 197, 3, "0,1,3,1,978,1"⟩,
  ⟨26, 197, 4, "0,5,1051,1"⟩,
  ⟨25, 197, 0, "1122,1"⟩,
  ⟨25, 197, 1, "13,3,294,1"⟩,
  ⟨25, 197, 2, "8,1,878,1"⟩,
  ⟨25, 197, 3, "0,1,1104,1"⟩,
  ⟨25, 197, 4, "0,3,1084,1"⟩,
  ⟨25, 197, 5, "0,3,1083,1"⟩,
  ⟨24, 197, 0, "1123,1"⟩,
  ⟨24, 197, 1, "13,4,181,1"⟩,
  ⟨24, 197, 2, "8,1,89,1,209,1"⟩,
  ⟨24, 197, 3, "0,1,1105,1"⟩,
  ⟨24, 197, 4, "0,1,67,1,359,1"⟩,
  ⟨23, 197, 0, "9,1,80,1,209,1"⟩,
  ⟨23, 197, 1, "0,1,68,1,359,1"⟩,
  ⟨23, 197, 2, "0,9,59,1,324,1"⟩,
  ⟨22, 197, 0, "0,1,18,1,690,1"⟩,
  ⟨22, 197, 1, "0,1,3,1,982,1"⟩,
  ⟨21, 197, 0, "1124,1"⟩,
  ⟨21, 197, 2, "0,1,1108,1"⟩,
  ⟨21, 197, 3, "0,1,3,1,984,1"⟩,
  ⟨20, 197, 0, "1125,1"⟩,
  ⟨20, 197, 1, "78,1,324,1"⟩,
  ⟨20, 197, 2, "0,1,67,1,363,1"⟩,
  ⟨19, 197, 1, "1,1,1096,1"⟩,
  ⟨19, 197, 2, "0,5,1055,1"⟩,
  ⟨18, 197, 1, "75,1,335,1"⟩,
  ⟨18, 197, 2, "2,2,1004,1"⟩,
  ⟨18, 197, 3, "0,3,1088,1"⟩,
  ⟨18, 197, 4, "0,5,1057,1"⟩,
  ⟨17, 197, 4, "0,1,1113,1"⟩,
  ⟨17, 197, 5, "0,6,64,1,324,1"⟩,
  ⟨16, 197, 1, "67,1,373,1"⟩,
  ⟨16, 197, 2, "8,2,20,1,324,1"⟩,
  ⟨16, 197, 3, "0,1,43,1,543,1"⟩,
  ⟨16, 197, 4, "0,2,1098,1"⟩,
  ⟨16, 197, 5, "0,5,66,1,324,1"⟩,
  ⟨15, 197, 2, "67,1,376,1"⟩,
  ⟨15, 197, 3, "8,1,45,1,324,1"⟩,
  ⟨15, 197, 4, "0,1,43,1,544,1"⟩,
  ⟨15, 197, 5, "0,1,2,1,1057,1"⟩,
  ⟨15, 197, 6, "0,2,1099,1"⟩,
  ⟨14, 197, 0, "1134,1"⟩,
  ⟨14, 197, 1, "1133,1"⟩,
  ⟨14, 197, 2, "1132,1"⟩,
  ⟨14, 197, 3, "8,1,46,1,324,1"⟩,
  ⟨14, 197, 4, "1,1,1100,1"⟩,
  ⟨14, 197, 5, "0,3,72,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row9178_mem, Shared.BasisChunk008.row9179_mem, Shared.BasisChunk008.row9180_mem, Shared.BasisChunk008.row9181_mem, Shared.BasisChunk008.row9182_mem, Shared.BasisChunk008.row9183_mem, Shared.BasisChunk008.row9184_mem, Shared.BasisChunk008.row9185_mem, Shared.BasisChunk008.row9186_mem, Shared.BasisChunk008.row9187_mem, Shared.BasisChunk008.row9188_mem, Shared.BasisChunk008.row9189_mem, Shared.BasisChunk008.row9192_mem, Shared.BasisChunk008.row9193_mem, Shared.BasisChunk008.row9194_mem, Shared.BasisChunk008.row9195_mem, Shared.BasisChunk008.row9196_mem, Shared.BasisChunk008.row9197_mem, Shared.BasisChunk008.row9198_mem, Shared.BasisChunk008.row9199_mem, Shared.BasisChunk008.row9200_mem, Shared.BasisChunk008.row9201_mem, Shared.BasisChunk008.row9202_mem, Shared.BasisChunk008.row9203_mem, Shared.BasisChunk008.row9204_mem, Shared.BasisChunk008.row9205_mem, Shared.BasisChunk008.row9206_mem, Shared.BasisChunk008.row9207_mem, Shared.BasisChunk008.row9208_mem, Shared.BasisChunk008.row9209_mem, Shared.BasisChunk008.row9210_mem, Shared.BasisChunk008.row9211_mem, Shared.BasisChunk008.row9212_mem, Shared.BasisChunk008.row9213_mem, Shared.BasisChunk008.row9214_mem, Shared.BasisChunk008.row9215_mem, Shared.BasisChunk009.row9216_mem, Shared.BasisChunk009.row9217_mem, Shared.BasisChunk009.row9218_mem, Shared.BasisChunk009.row9219_mem, Shared.BasisChunk009.row9220_mem, Shared.BasisChunk009.row9221_mem, Shared.BasisChunk009.row9223_mem, Shared.BasisChunk009.row9224_mem, Shared.BasisChunk009.row9225_mem, Shared.BasisChunk009.row9226_mem, Shared.BasisChunk009.row9227_mem, Shared.BasisChunk009.row9229_mem, Shared.BasisChunk009.row9230_mem, Shared.BasisChunk009.row9232_mem, Shared.BasisChunk009.row9233_mem, Shared.BasisChunk009.row9234_mem, Shared.BasisChunk009.row9235_mem, Shared.BasisChunk009.row9240_mem, Shared.BasisChunk009.row9241_mem, Shared.BasisChunk009.row9243_mem, Shared.BasisChunk009.row9244_mem, Shared.BasisChunk009.row9245_mem, Shared.BasisChunk009.row9246_mem, Shared.BasisChunk009.row9247_mem, Shared.BasisChunk009.row9250_mem, Shared.BasisChunk009.row9251_mem, Shared.BasisChunk009.row9252_mem, Shared.BasisChunk009.row9253_mem, Shared.BasisChunk009.row9254_mem, Shared.BasisChunk009.row9255_mem, Shared.BasisChunk009.row9256_mem, Shared.BasisChunk009.row9257_mem, Shared.BasisChunk009.row9258_mem, Shared.BasisChunk009.row9259_mem, Shared.BasisChunk009.row9260_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard121
