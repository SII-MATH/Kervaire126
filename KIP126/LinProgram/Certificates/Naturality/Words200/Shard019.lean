module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard019
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard019
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard019
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation45_zero, Shared.RelationChunk000.relation46_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation97_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk003.relation277_zero, Shared.RelationChunk003.relation279_zero, Shared.RelationChunk003.relation280_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation282_zero, Shared.RelationChunk003.relation284_zero, Shared.RelationChunk003.relation286_zero, Shared.RelationChunk003.relation287_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2434 128 := by cbv
private def targetRows : List BasisRow := [⟨7, 107, 0, "0,1,34,1,69,1"⟩,
  ⟨108, 108, 0, "0,108"⟩,
  ⟨35, 108, 0, "0,3,199,1"⟩,
  ⟨31, 108, 0, "16,1,111,1"⟩,
  ⟨30, 108, 0, "17,1,111,1"⟩,
  ⟨29, 108, 0, "211,1"⟩,
  ⟨28, 108, 0, "8,3,49,1"⟩,
  ⟨27, 108, 0, "8,3,50,1"⟩,
  ⟨26, 108, 0, "8,1,16,1,17,2"⟩,
  ⟨25, 108, 0, "8,2,88,1"⟩,
  ⟨24, 108, 0, "8,6"⟩,
  ⟨23, 108, 0, "8,4,22,1"⟩,
  ⟨22, 108, 1, "8,4,23,1"⟩,
  ⟨21, 108, 0, "8,1,147,1"⟩,
  ⟨21, 108, 1, "8,3,51,1"⟩,
  ⟨21, 108, 2, "0,1,206,1"⟩,
  ⟨20, 108, 0, "17,1,113,1"⟩,
  ⟨20, 108, 1, "8,2,13,3"⟩,
  ⟨19, 108, 0, "8,1,13,2,32,1"⟩,
  ⟨19, 108, 1, "0,1,207,1"⟩,
  ⟨18, 108, 0, "13,3,23,1"⟩,
  ⟨18, 108, 2, "0,6,187,1"⟩,
  ⟨17, 108, 0, "13,3,24,1"⟩,
  ⟨17, 108, 1, "8,1,9,1,80,1"⟩,
  ⟨17, 108, 2, "0,6,188,1"⟩,
  ⟨16, 108, 0, "23,1,89,1"⟩,
  ⟨15, 108, 0, "0,2,31,1,69,1"⟩,
  ⟨15, 108, 1, "0,3,201,1"⟩,
  ⟨13, 108, 0, "2,1,195,1"⟩,
  ⟨12, 108, 1, "3,1,178,1"⟩,
  ⟨11, 108, 0, "0,1,209,1"⟩,
  ⟨11, 108, 1, "0,2,8,1,13,1,69,1"⟩,
  ⟨10, 108, 0, "0,1,3,1,174,1"⟩,
  ⟨10, 108, 1, "0,2,32,1,69,1"⟩,
  ⟨9, 108, 1, "0,2,203,1"⟩,
  ⟨8, 108, 0, "2,1,198,1"⟩,
  ⟨8, 108, 2, "1,1,33,1,69,1"⟩,
  ⟨8, 108, 3, "0,2,34,1,69,1"⟩,
  ⟨7, 108, 2, "1,1,34,1,69,1"⟩,
  ⟨4, 108, 0, "38,1,69,1"⟩,
  ⟨109, 109, 0, "0,109"⟩,
  ⟨36, 109, 0, "1,1,205,1"⟩,
  ⟨33, 109, 0, "0,1,8,1,145,1"⟩,
  ⟨32, 109, 0, "0,1,16,1,111,1"⟩,
  ⟨31, 109, 0, "0,1,17,1,111,1"⟩,
  ⟨30, 109, 0, "0,1,210,1"⟩,
  ⟨23, 109, 0, "0,1,8,1,146,1"⟩,
  ⟨22, 109, 0, "0,1,8,1,147,1"⟩,
  ⟨22, 109, 1, "0,2,206,1"⟩,
  ⟨21, 109, 0, "0,1,17,1,113,1"⟩,
  ⟨19, 109, 0, "0,7,187,1"⟩,
  ⟨18, 109, 0, "0,7,188,1"⟩,
  ⟨14, 109, 0, "0,1,2,1,195,1"⟩,
  ⟨13, 109, 1, "13,1,133,1"⟩,
  ⟨13, 109, 2, "0,1,212,1"⟩,
  ⟨12, 109, 0, "40,1,69,1"⟩,
  ⟨12, 109, 1, "13,1,134,1"⟩,
  ⟨12, 109, 2, "0,2,209,1"⟩,
  ⟨11, 109, 0, "2,1,202,1"⟩,
  ⟨10, 109, 0, "2,2,181,1"⟩,
  ⟨10, 109, 1, "0,3,203,1"⟩,
  ⟨9, 109, 1, "3,1,181,1"⟩,
  ⟨9, 109, 2, "0,3,34,1,69,1"⟩,
  ⟨8, 109, 1, "0,1,36,1,69,1"⟩,
  ⟨6, 109, 0, "0,1,37,1,69,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1467_mem, Shared.BasisChunk001.row1468_mem, Shared.BasisChunk001.row1469_mem, Shared.BasisChunk001.row1471_mem, Shared.BasisChunk001.row1472_mem, Shared.BasisChunk001.row1473_mem, Shared.BasisChunk001.row1475_mem, Shared.BasisChunk001.row1476_mem, Shared.BasisChunk001.row1477_mem, Shared.BasisChunk001.row1478_mem, Shared.BasisChunk001.row1479_mem, Shared.BasisChunk001.row1480_mem, Shared.BasisChunk001.row1482_mem, Shared.BasisChunk001.row1484_mem, Shared.BasisChunk001.row1485_mem, Shared.BasisChunk001.row1486_mem, Shared.BasisChunk001.row1487_mem, Shared.BasisChunk001.row1488_mem, Shared.BasisChunk001.row1489_mem, Shared.BasisChunk001.row1490_mem, Shared.BasisChunk001.row1491_mem, Shared.BasisChunk001.row1493_mem, Shared.BasisChunk001.row1494_mem, Shared.BasisChunk001.row1495_mem, Shared.BasisChunk001.row1496_mem, Shared.BasisChunk001.row1497_mem, Shared.BasisChunk001.row1498_mem, Shared.BasisChunk001.row1499_mem, Shared.BasisChunk001.row1501_mem, Shared.BasisChunk001.row1503_mem, Shared.BasisChunk001.row1504_mem, Shared.BasisChunk001.row1505_mem, Shared.BasisChunk001.row1506_mem, Shared.BasisChunk001.row1507_mem, Shared.BasisChunk001.row1509_mem, Shared.BasisChunk001.row1510_mem, Shared.BasisChunk001.row1512_mem, Shared.BasisChunk001.row1513_mem, Shared.BasisChunk001.row1516_mem, Shared.BasisChunk001.row1519_mem, Shared.BasisChunk001.row1520_mem, Shared.BasisChunk001.row1521_mem, Shared.BasisChunk001.row1522_mem, Shared.BasisChunk001.row1523_mem, Shared.BasisChunk001.row1524_mem, Shared.BasisChunk001.row1525_mem, Shared.BasisChunk001.row1526_mem, Shared.BasisChunk001.row1527_mem, Shared.BasisChunk001.row1528_mem, Shared.BasisChunk001.row1529_mem, Shared.BasisChunk001.row1530_mem, Shared.BasisChunk001.row1531_mem, Shared.BasisChunk001.row1533_mem, Shared.BasisChunk001.row1535_mem, Shared.BasisChunk001.row1536_mem, Shared.BasisChunk001.row1537_mem, Shared.BasisChunk001.row1538_mem, Shared.BasisChunk001.row1539_mem, Shared.BasisChunk001.row1540_mem, Shared.BasisChunk001.row1542_mem, Shared.BasisChunk001.row1543_mem, Shared.BasisChunk001.row1545_mem, Shared.BasisChunk001.row1546_mem, Shared.BasisChunk001.row1548_mem, Shared.BasisChunk001.row1549_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard019
