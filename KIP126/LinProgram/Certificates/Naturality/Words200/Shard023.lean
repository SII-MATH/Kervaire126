import KIP126.LinProgram.Generated.Naturality.Words200.Shard023
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard023
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard023
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
  exact ⟨Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation154_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk002.relation214_zero, Shared.RelationChunk002.relation215_zero, Shared.RelationChunk002.relation216_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk002.relation239_zero, Shared.RelationChunk002.relation240_zero, Shared.RelationChunk002.relation241_zero, Shared.RelationChunk004.relation323_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation327_zero, Shared.RelationChunk005.relation329_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk005.relation331_zero, Shared.RelationChunk005.relation332_zero, Shared.RelationChunk005.relation333_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2946 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 116, 0, "0,2,8,2,113,1"⟩,
  ⟨21, 116, 0, "247,1"⟩,
  ⟨20, 116, 0, "8,1,166,1"⟩,
  ⟨19, 116, 0, "8,1,167,1"⟩,
  ⟨18, 116, 0, "248,1"⟩,
  ⟨17, 116, 0, "13,1,150,1"⟩,
  ⟨16, 116, 0, "13,1,151,1"⟩,
  ⟨15, 116, 0, "2,1,228,1"⟩,
  ⟨14, 116, 1, "0,1,8,1,19,1,69,1"⟩,
  ⟨13, 116, 0, "0,1,8,1,20,1,69,1"⟩,
  ⟨12, 116, 1, "0,1,3,1,209,1"⟩,
  ⟨12, 116, 2, "0,3,235,1"⟩,
  ⟨11, 116, 0, "0,1,43,1,74,1"⟩,
  ⟨11, 116, 1, "0,1,3,2,174,1"⟩,
  ⟨6, 116, 0, "2,1,7,1,163,1"⟩,
  ⟨5, 116, 0, "3,1,38,1,69,1"⟩,
  ⟨117, 117, 0, "0,117"⟩,
  ⟨38, 117, 0, "0,9,210,1"⟩,
  ⟨35, 117, 0, "253,1"⟩,
  ⟨32, 117, 1, "0,6,224,1"⟩,
  ⟨31, 117, 0, "8,2,117,1"⟩,
  ⟨31, 117, 1, "0,6,225,1"⟩,
  ⟨30, 117, 0, "8,1,17,1,78,1"⟩,
  ⟨29, 117, 0, "8,1,171,1"⟩,
  ⟨29, 117, 1, "0,3,237,1"⟩,
  ⟨28, 117, 0, "8,4,39,1"⟩,
  ⟨27, 117, 0, "8,4,40,1"⟩,
  ⟨26, 117, 1, "8,3,17,1,20,1"⟩,
  ⟨25, 117, 0, "16,1,138,1"⟩,
  ⟨25, 117, 1, "8,3,63,1"⟩,
  ⟨25, 117, 2, "0,1,244,1"⟩,
  ⟨24, 117, 0, "17,1,138,1"⟩,
  ⟨24, 117, 1, "8,4,9,1,13,1"⟩,
  ⟨23, 117, 0, "8,3,9,1,32,1"⟩,
  ⟨23, 117, 1, "0,1,245,1"⟩,
  ⟨22, 117, 0, "8,2,9,1,13,1,23,1"⟩,
  ⟨22, 117, 2, "0,1,246,1"⟩,
  ⟨21, 117, 0, "8,1,9,1,13,1,51,1"⟩,
  ⟨21, 117, 1, "8,2,118,1"⟩,
  ⟨20, 117, 0, "9,1,13,4"⟩,
  ⟨20, 117, 1, "8,1,17,1,80,1"⟩,
  ⟨19, 117, 0, "8,1,173,1"⟩,
  ⟨18, 117, 0, "8,1,13,1,101,1"⟩,
  ⟨17, 117, 0, "13,2,80,1"⟩,
  ⟨15, 117, 0, "255,1"⟩,
  ⟨14, 117, 0, "0,2,8,1,20,1,69,1"⟩,
  ⟨13, 117, 0, "0,1,250,1"⟩,
  ⟨13, 117, 1, "0,4,235,1"⟩,
  ⟨10, 117, 0, "0,1,251,1"⟩,
  ⟨7, 117, 0, "0,1,2,1,7,1,163,1"⟩,
  ⟨118, 118, 0, "0,118"⟩,
  ⟨39, 118, 0, "0,10,210,1"⟩,
  ⟨37, 118, 0, "0,1,252,1"⟩,
  ⟨36, 118, 0, "0,1,253,1"⟩,
  ⟨33, 118, 0, "0,7,224,1"⟩,
  ⟨32, 118, 0, "0,7,225,1"⟩,
  ⟨27, 118, 0, "0,1,16,1,137,1"⟩,
  ⟨26, 118, 0, "0,1,16,1,138,1"⟩,
  ⟨26, 118, 1, "0,2,244,1"⟩,
  ⟨25, 118, 1, "0,1,17,1,138,1"⟩,
  ⟨24, 118, 0, "0,2,245,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1779_mem, Shared.BasisChunk001.row1781_mem, Shared.BasisChunk001.row1783_mem, Shared.BasisChunk001.row1784_mem, Shared.BasisChunk001.row1785_mem, Shared.BasisChunk001.row1786_mem, Shared.BasisChunk001.row1788_mem, Shared.BasisChunk001.row1789_mem, Shared.BasisChunk001.row1791_mem, Shared.BasisChunk001.row1792_mem, Shared.BasisChunk001.row1794_mem, Shared.BasisChunk001.row1795_mem, Shared.BasisChunk001.row1796_mem, Shared.BasisChunk001.row1797_mem, Shared.BasisChunk001.row1801_mem, Shared.BasisChunk001.row1802_mem, Shared.BasisChunk001.row1803_mem, Shared.BasisChunk001.row1804_mem, Shared.BasisChunk001.row1806_mem, Shared.BasisChunk001.row1808_mem, Shared.BasisChunk001.row1809_mem, Shared.BasisChunk001.row1810_mem, Shared.BasisChunk001.row1811_mem, Shared.BasisChunk001.row1812_mem, Shared.BasisChunk001.row1813_mem, Shared.BasisChunk001.row1814_mem, Shared.BasisChunk001.row1815_mem, Shared.BasisChunk001.row1817_mem, Shared.BasisChunk001.row1818_mem, Shared.BasisChunk001.row1819_mem, Shared.BasisChunk001.row1820_mem, Shared.BasisChunk001.row1821_mem, Shared.BasisChunk001.row1822_mem, Shared.BasisChunk001.row1823_mem, Shared.BasisChunk001.row1824_mem, Shared.BasisChunk001.row1825_mem, Shared.BasisChunk001.row1827_mem, Shared.BasisChunk001.row1828_mem, Shared.BasisChunk001.row1829_mem, Shared.BasisChunk001.row1830_mem, Shared.BasisChunk001.row1831_mem, Shared.BasisChunk001.row1832_mem, Shared.BasisChunk001.row1833_mem, Shared.BasisChunk001.row1834_mem, Shared.BasisChunk001.row1836_mem, Shared.BasisChunk001.row1837_mem, Shared.BasisChunk001.row1838_mem, Shared.BasisChunk001.row1839_mem, Shared.BasisChunk001.row1840_mem, Shared.BasisChunk001.row1843_mem, Shared.BasisChunk001.row1844_mem, Shared.BasisChunk001.row1845_mem, Shared.BasisChunk001.row1847_mem, Shared.BasisChunk001.row1848_mem, Shared.BasisChunk001.row1849_mem, Shared.BasisChunk001.row1850_mem, Shared.BasisChunk001.row1851_mem, Shared.BasisChunk001.row1852_mem, Shared.BasisChunk001.row1853_mem, Shared.BasisChunk001.row1855_mem, Shared.BasisChunk001.row1856_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard023
