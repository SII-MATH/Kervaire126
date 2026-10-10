import KIP126.LinProgram.Generated.Naturality.Words200.Shard020
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard020
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard020
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation51_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, Shared.RelationChunk000.relation138_zero, Shared.RelationChunk001.relation181_zero, Shared.RelationChunk001.relation182_zero, Shared.RelationChunk001.relation184_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk002.relation214_zero, Shared.RelationChunk002.relation216_zero, Shared.RelationChunk002.relation218_zero, Shared.RelationChunk002.relation220_zero, Shared.RelationChunk002.relation221_zero, Shared.RelationChunk003.relation288_zero, Shared.RelationChunk003.relation289_zero, Shared.RelationChunk003.relation290_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk004.relation293_zero, Shared.RelationChunk004.relation297_zero, Shared.RelationChunk004.relation298_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2562 128 := by cbv
private def targetRows : List BasisRow := [⟨5, 109, 0, "0,1,38,1,69,1"⟩,
  ⟨110, 110, 0, "0,110"⟩,
  ⟨34, 110, 0, "0,2,8,1,145,1"⟩,
  ⟨33, 110, 0, "0,2,16,1,111,1"⟩,
  ⟨32, 110, 0, "0,2,17,1,111,1"⟩,
  ⟨31, 110, 0, "0,2,210,1"⟩,
  ⟨24, 110, 0, "0,2,8,1,146,1"⟩,
  ⟨23, 110, 0, "0,2,8,1,147,1"⟩,
  ⟨23, 110, 1, "0,3,206,1"⟩,
  ⟨19, 110, 0, "0,8,188,1"⟩,
  ⟨18, 110, 0, "218,1"⟩,
  ⟨17, 110, 0, "219,1"⟩,
  ⟨16, 110, 0, "220,1"⟩,
  ⟨15, 110, 0, "1,2,31,1,69,1"⟩,
  ⟨14, 110, 0, "0,1,39,1,69,1"⟩,
  ⟨14, 110, 1, "0,2,212,1"⟩,
  ⟨13, 110, 0, "1,1,212,1"⟩,
  ⟨13, 110, 1, "0,1,40,1,69,1"⟩,
  ⟨13, 110, 2, "0,3,209,1"⟩,
  ⟨12, 110, 1, "2,2,189,1"⟩,
  ⟨10, 110, 0, "221,1"⟩,
  ⟨10, 110, 2, "0,4,34,1,69,1"⟩,
  ⟨9, 110, 1, "1,2,203,1"⟩,
  ⟨9, 110, 2, "0,1,216,1"⟩,
  ⟨9, 110, 3, "0,2,36,1,69,1"⟩,
  ⟨8, 110, 0, "3,1,191,1"⟩,
  ⟨8, 110, 1, "1,1,214,1"⟩,
  ⟨8, 110, 2, "1,1,36,1,69,1"⟩,
  ⟨7, 110, 0, "222,1"⟩,
  ⟨7, 110, 1, "0,2,37,1,69,1"⟩,
  ⟨6, 110, 0, "0,2,38,1,69,1"⟩,
  ⟨111, 111, 0, "0,111"⟩,
  ⟨33, 111, 0, "0,3,17,1,111,1"⟩,
  ⟨32, 111, 1, "0,3,210,1"⟩,
  ⟨31, 111, 0, "8,1,153,1"⟩,
  ⟨30, 111, 0, "17,1,117,1"⟩,
  ⟨29, 111, 0, "223,1"⟩,
  ⟨28, 111, 0, "8,3,55,1"⟩,
  ⟨27, 111, 0, "8,3,56,1"⟩,
  ⟨26, 111, 1, "8,2,17,1,40,1"⟩,
  ⟨25, 111, 0, "225,1"⟩,
  ⟨25, 111, 1, "8,2,100,1"⟩,
  ⟨24, 111, 0, "8,5,9,1"⟩,
  ⟨23, 111, 0, "8,4,29,1"⟩,
  ⟨22, 111, 1, "8,3,9,1,23,1"⟩,
  ⟨21, 111, 0, "8,1,17,1,64,1"⟩,
  ⟨21, 111, 1, "8,2,9,1,51,1"⟩,
  ⟨21, 111, 2, "0,1,8,1,149,1"⟩,
  ⟨20, 111, 0, "8,1,154,1"⟩,
  ⟨20, 111, 1, "8,1,9,1,13,3"⟩,
  ⟨19, 111, 1, "9,1,13,2,32,1"⟩,
  ⟨18, 111, 0, "8,2,101,1"⟩,
  ⟨17, 111, 0, "8,1,13,1,80,1"⟩,
  ⟨16, 111, 1, "23,1,101,1"⟩,
  ⟨15, 111, 0, "226,1"⟩,
  ⟨15, 111, 1, "0,2,39,1,69,1"⟩,
  ⟨14, 111, 0, "0,2,40,1,69,1"⟩,
  ⟨14, 111, 1, "0,4,209,1"⟩,
  ⟨13, 111, 0, "0,1,3,1,188,1"⟩,
  ⟨12, 111, 1, "0,1,3,1,189,1"⟩,
  ⟨11, 111, 0, "2,1,209,1"⟩,
  ⟨11, 111, 1, "0,1,221,1"⟩,
  ⟨11, 111, 2, "0,5,34,1,69,1"⟩,
  ⟨10, 111, 0, "0,2,216,1"⟩,
  ⟨10, 111, 1, "0,3,36,1,69,1"⟩,
  ⟨9, 111, 0, "0,1,3,1,191,1"⟩,
  ⟨112, 112, 0, "0,112"⟩,
  ⟨37, 112, 0, "227,1"⟩,
  ⟨34, 112, 0, "0,4,17,1,111,1"⟩,
  ⟨33, 112, 0, "0,1,8,1,152,1"⟩,
  ⟨33, 112, 1, "0,4,210,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1550_mem, Shared.BasisChunk001.row1551_mem, Shared.BasisChunk001.row1553_mem, Shared.BasisChunk001.row1554_mem, Shared.BasisChunk001.row1555_mem, Shared.BasisChunk001.row1556_mem, Shared.BasisChunk001.row1558_mem, Shared.BasisChunk001.row1559_mem, Shared.BasisChunk001.row1560_mem, Shared.BasisChunk001.row1562_mem, Shared.BasisChunk001.row1563_mem, Shared.BasisChunk001.row1564_mem, Shared.BasisChunk001.row1565_mem, Shared.BasisChunk001.row1566_mem, Shared.BasisChunk001.row1567_mem, Shared.BasisChunk001.row1568_mem, Shared.BasisChunk001.row1569_mem, Shared.BasisChunk001.row1570_mem, Shared.BasisChunk001.row1571_mem, Shared.BasisChunk001.row1573_mem, Shared.BasisChunk001.row1575_mem, Shared.BasisChunk001.row1577_mem, Shared.BasisChunk001.row1579_mem, Shared.BasisChunk001.row1580_mem, Shared.BasisChunk001.row1581_mem, Shared.BasisChunk001.row1582_mem, Shared.BasisChunk001.row1583_mem, Shared.BasisChunk001.row1584_mem, Shared.BasisChunk001.row1585_mem, Shared.BasisChunk001.row1586_mem, Shared.BasisChunk001.row1587_mem, Shared.BasisChunk001.row1588_mem, Shared.BasisChunk001.row1589_mem, Shared.BasisChunk001.row1591_mem, Shared.BasisChunk001.row1592_mem, Shared.BasisChunk001.row1593_mem, Shared.BasisChunk001.row1594_mem, Shared.BasisChunk001.row1595_mem, Shared.BasisChunk001.row1596_mem, Shared.BasisChunk001.row1598_mem, Shared.BasisChunk001.row1599_mem, Shared.BasisChunk001.row1600_mem, Shared.BasisChunk001.row1601_mem, Shared.BasisChunk001.row1602_mem, Shared.BasisChunk001.row1604_mem, Shared.BasisChunk001.row1605_mem, Shared.BasisChunk001.row1606_mem, Shared.BasisChunk001.row1607_mem, Shared.BasisChunk001.row1608_mem, Shared.BasisChunk001.row1609_mem, Shared.BasisChunk001.row1611_mem, Shared.BasisChunk001.row1612_mem, Shared.BasisChunk001.row1613_mem, Shared.BasisChunk001.row1615_mem, Shared.BasisChunk001.row1617_mem, Shared.BasisChunk001.row1618_mem, Shared.BasisChunk001.row1619_mem, Shared.BasisChunk001.row1620_mem, Shared.BasisChunk001.row1621_mem, Shared.BasisChunk001.row1623_mem, Shared.BasisChunk001.row1624_mem, Shared.BasisChunk001.row1625_mem, Shared.BasisChunk001.row1626_mem, Shared.BasisChunk001.row1627_mem, Shared.BasisChunk001.row1628_mem, Shared.BasisChunk001.row1629_mem, Shared.BasisChunk001.row1630_mem, Shared.BasisChunk001.row1632_mem, Shared.BasisChunk001.row1633_mem, Shared.BasisChunk001.row1634_mem, Shared.BasisChunk001.row1635_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard020
