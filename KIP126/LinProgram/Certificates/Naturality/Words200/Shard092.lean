module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard092
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk033
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard092
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard092
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation71_zero, Shared.RelationChunk000.relation72_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk003.relation278_zero, Shared.RelationChunk003.relation279_zero, Shared.RelationChunk003.relation280_zero, Shared.RelationChunk003.relation285_zero, Shared.RelationChunk004.relation309_zero, Shared.RelationChunk004.relation310_zero, Shared.RelationChunk004.relation311_zero, Shared.RelationChunk004.relation312_zero, Shared.RelationChunk004.relation324_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation395_zero, Shared.RelationChunk006.relation396_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk012.relation622_zero, Shared.RelationChunk012.relation623_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk012.relation625_zero, Shared.RelationChunk012.relation626_zero, Shared.RelationChunk012.relation630_zero, Shared.RelationChunk014.relation738_zero, Shared.RelationChunk017.relation833_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk017.relation839_zero, Shared.RelationChunk019.relation890_zero, Shared.RelationChunk020.relation941_zero, Shared.RelationChunk021.relation945_zero, Shared.RelationChunk021.relation946_zero, Shared.RelationChunk021.relation947_zero, Shared.RelationChunk033.relation1369_zero, Shared.RelationChunk033.relation1370_zero, Shared.RelationChunk033.relation1380_zero, Shared.RelationChunk034.relation1386_zero, Shared.RelationChunk034.relation1401_zero, Shared.RelationChunk034.relation1402_zero, Shared.RelationChunk034.relation1403_zero, Shared.RelationChunk034.relation1404_zero, Shared.RelationChunk034.relation1405_zero, Shared.RelationChunk034.relation1406_zero, Shared.RelationChunk034.relation1407_zero, Shared.RelationChunk034.relation1408_zero, Shared.RelationChunk034.relation1409_zero, Shared.RelationChunk034.relation1410_zero, Shared.RelationChunk034.relation1411_zero, Shared.RelationChunk034.relation1419_zero, Shared.RelationChunk034.relation1420_zero, Shared.RelationChunk034.relation1421_zero, Shared.RelationChunk034.relation1422_zero, Shared.RelationChunk034.relation1423_zero, Shared.RelationChunk034.relation1424_zero, Shared.RelationChunk034.relation1425_zero, Shared.RelationChunk034.relation1426_zero, Shared.RelationChunk034.relation1427_zero, Shared.RelationChunk034.relation1428_zero, Shared.RelationChunk034.relation1429_zero, Shared.RelationChunk034.relation1430_zero, Shared.RelationChunk035.relation1431_zero, Shared.RelationChunk035.relation1432_zero, Shared.RelationChunk035.relation1433_zero, Shared.RelationChunk035.relation1434_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11778 128 := by cbv
private def targetRows : List BasisRow := [⟨33, 180, 0, "8,1,665,1"⟩,
  ⟨33, 180, 1, "8,3,13,3,51,1"⟩,
  ⟨33, 180, 2, "8,5,9,1,80,1"⟩,
  ⟨33, 180, 3, "0,1,17,2,260,1"⟩,
  ⟨32, 180, 0, "8,2,13,6"⟩,
  ⟨32, 180, 1, "8,3,64,2"⟩,
  ⟨32, 180, 2, "8,4,23,1,89,1"⟩,
  ⟨32, 180, 3, "0,1,64,1,246,1"⟩,
  ⟨32, 180, 4, "0,1,59,1,260,1"⟩,
  ⟨31, 180, 0, "8,1,13,5,32,1"⟩,
  ⟨31, 180, 1, "8,3,299,1"⟩,
  ⟨31, 180, 2, "8,3,9,1,23,1,80,1"⟩,
  ⟨31, 180, 3, "0,2,862,1"⟩,
  ⟨30, 180, 0, "13,6,23,1"⟩,
  ⟨30, 180, 1, "8,2,499,1"⟩,
  ⟨30, 180, 2, "8,2,9,1,13,2,101,1"⟩,
  ⟨29, 180, 0, "13,6,24,1"⟩,
  ⟨29, 180, 1, "8,1,13,1,435,1"⟩,
  ⟨29, 180, 2, "8,1,9,1,13,3,80,1"⟩,
  ⟨28, 180, 0, "9,1,13,2,23,1,101,1"⟩,
  ⟨28, 180, 1, "8,4,212,1"⟩,
  ⟨27, 180, 0, "8,3,13,1,188,1"⟩,
  ⟨26, 180, 0, "64,1,254,1"⟩,
  ⟨26, 180, 1, "8,2,13,1,267,1"⟩,
  ⟨25, 180, 0, "64,1,255,1"⟩,
  ⟨25, 180, 1, "13,2,357,1"⟩,
  ⟨25, 180, 2, "8,1,13,1,23,1,188,1"⟩,
  ⟨25, 180, 3, "0,1,8,1,655,1"⟩,
  ⟨24, 180, 0, "13,3,212,1"⟩,
  ⟨24, 180, 1, "9,1,23,1,286,1"⟩,
  ⟨24, 180, 2, "8,1,667,1"⟩,
  ⟨24, 180, 3, "0,1,875,1"⟩,
  ⟨24, 180, 4, "0,1,874,1"⟩,
  ⟨23, 180, 0, "887,1"⟩,
  ⟨23, 180, 1, "13,2,360,1"⟩,
  ⟨23, 180, 2, "8,1,668,1"⟩,
  ⟨23, 180, 3, "0,1,876,1"⟩,
  ⟨23, 180, 4, "0,1,64,1,250,1"⟩,
  ⟨23, 180, 5, "0,4,64,1,235,1"⟩,
  ⟨23, 180, 6, "0,12,743,1"⟩,
  ⟨22, 180, 0, "9,1,640,1"⟩,
  ⟨22, 180, 1, "2,1,833,1"⟩,
  ⟨22, 180, 2, "0,4,837,1"⟩,
  ⟨22, 180, 3, "0,4,836,1"⟩,
  ⟨21, 180, 0, "13,3,213,1"⟩,
  ⟨21, 180, 1, "0,4,838,1"⟩,
  ⟨20, 180, 0, "9,1,13,1,408,1"⟩,
  ⟨20, 180, 1, "1,2,836,1"⟩,
  ⟨20, 180, 2, "0,1,879,1"⟩,
  ⟨20, 180, 3, "0,5,825,1"⟩,
  ⟨19, 180, 0, "1,1,865,1"⟩,
  ⟨19, 180, 1, "1,1,44,1,324,1"⟩,
  ⟨19, 180, 2, "1,2,838,1"⟩,
  ⟨19, 180, 3, "0,1,880,1"⟩,
  ⟨19, 180, 4, "0,2,3,1,763,1"⟩,
  ⟨18, 180, 0, "47,1,324,1"⟩,
  ⟨18, 180, 1, "7,1,692,1"⟩,
  ⟨18, 180, 2, "1,1,866,1"⟩,
  ⟨18, 180, 3, "0,2,3,1,764,1"⟩,
  ⟨17, 180, 0, "1,1,3,1,764,1"⟩,
  ⟨16, 180, 0, "0,1,92,1,209,1"⟩,
  ⟨16, 180, 1, "0,3,858,1"⟩,
  ⟨15, 180, 0, "2,1,843,1"⟩,
  ⟨15, 180, 1, "1,1,868,1"⟩,
  ⟨15, 180, 2, "0,1,882,1"⟩,
  ⟨15, 180, 3, "0,1,8,1,18,1,333,1"⟩,
  ⟨14, 180, 0, "3,1,787,1"⟩,
  ⟨14, 180, 1, "0,1,8,1,659,1"⟩,
  ⟨14, 180, 2, "0,1,8,1,19,1,324,1"⟩,
  ⟨14, 180, 3, "0,2,869,1"⟩,
  ⟨13, 180, 1, "0,1,883,1"⟩,
  ⟨13, 180, 2, "0,1,43,1,352,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row7057_mem, Shared.BasisChunk006.row7058_mem, Shared.BasisChunk006.row7059_mem, Shared.BasisChunk006.row7060_mem, Shared.BasisChunk006.row7061_mem, Shared.BasisChunk006.row7062_mem, Shared.BasisChunk006.row7063_mem, Shared.BasisChunk006.row7064_mem, Shared.BasisChunk006.row7065_mem, Shared.BasisChunk006.row7066_mem, Shared.BasisChunk006.row7067_mem, Shared.BasisChunk006.row7068_mem, Shared.BasisChunk006.row7069_mem, Shared.BasisChunk006.row7070_mem, Shared.BasisChunk006.row7071_mem, Shared.BasisChunk006.row7072_mem, Shared.BasisChunk006.row7074_mem, Shared.BasisChunk006.row7075_mem, Shared.BasisChunk006.row7076_mem, Shared.BasisChunk006.row7077_mem, Shared.BasisChunk006.row7078_mem, Shared.BasisChunk006.row7079_mem, Shared.BasisChunk006.row7080_mem, Shared.BasisChunk006.row7081_mem, Shared.BasisChunk006.row7082_mem, Shared.BasisChunk006.row7083_mem, Shared.BasisChunk006.row7084_mem, Shared.BasisChunk006.row7085_mem, Shared.BasisChunk006.row7086_mem, Shared.BasisChunk006.row7087_mem, Shared.BasisChunk006.row7088_mem, Shared.BasisChunk006.row7089_mem, Shared.BasisChunk006.row7090_mem, Shared.BasisChunk006.row7091_mem, Shared.BasisChunk006.row7092_mem, Shared.BasisChunk006.row7093_mem, Shared.BasisChunk006.row7094_mem, Shared.BasisChunk006.row7095_mem, Shared.BasisChunk006.row7096_mem, Shared.BasisChunk006.row7097_mem, Shared.BasisChunk006.row7098_mem, Shared.BasisChunk006.row7099_mem, Shared.BasisChunk006.row7100_mem, Shared.BasisChunk006.row7101_mem, Shared.BasisChunk006.row7102_mem, Shared.BasisChunk006.row7103_mem, Shared.BasisChunk006.row7104_mem, Shared.BasisChunk006.row7105_mem, Shared.BasisChunk006.row7106_mem, Shared.BasisChunk006.row7107_mem, Shared.BasisChunk006.row7108_mem, Shared.BasisChunk006.row7109_mem, Shared.BasisChunk006.row7110_mem, Shared.BasisChunk006.row7111_mem, Shared.BasisChunk006.row7112_mem, Shared.BasisChunk006.row7113_mem, Shared.BasisChunk006.row7114_mem, Shared.BasisChunk006.row7115_mem, Shared.BasisChunk006.row7116_mem, Shared.BasisChunk006.row7117_mem, Shared.BasisChunk006.row7118_mem, Shared.BasisChunk006.row7119_mem, Shared.BasisChunk006.row7120_mem, Shared.BasisChunk006.row7121_mem, Shared.BasisChunk006.row7122_mem, Shared.BasisChunk006.row7123_mem, Shared.BasisChunk006.row7124_mem, Shared.BasisChunk006.row7125_mem, Shared.BasisChunk006.row7126_mem, Shared.BasisChunk006.row7127_mem, Shared.BasisChunk006.row7129_mem, Shared.BasisChunk006.row7130_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard092
