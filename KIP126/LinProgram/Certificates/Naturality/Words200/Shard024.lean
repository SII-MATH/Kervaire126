module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard024
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard024
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard024
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk001.relation171_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation223_zero, Shared.RelationChunk003.relation252_zero, Shared.RelationChunk003.relation255_zero, Shared.RelationChunk005.relation334_zero, Shared.RelationChunk005.relation335_zero, Shared.RelationChunk005.relation336_zero, Shared.RelationChunk005.relation337_zero, Shared.RelationChunk005.relation338_zero, Shared.RelationChunk005.relation339_zero, Shared.RelationChunk005.relation341_zero, Shared.RelationChunk005.relation342_zero, Shared.RelationChunk005.relation352_zero, Shared.RelationChunk005.relation353_zero, Shared.RelationChunk005.relation354_zero, Shared.RelationChunk005.relation355_zero, Shared.RelationChunk005.relation356_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3074 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 118, 0, "0,1,8,3,64,1"⟩,
  ⟨23, 118, 1, "0,2,246,1"⟩,
  ⟨22, 118, 1, "0,1,8,2,118,1"⟩,
  ⟨18, 118, 0, "1,1,5,1,187,1"⟩,
  ⟨17, 118, 1, "0,1,254,1"⟩,
  ⟨16, 118, 0, "50,1,69,1"⟩,
  ⟨16, 118, 1, "13,2,83,1"⟩,
  ⟨16, 118, 2, "0,1,255,1"⟩,
  ⟨15, 118, 0, "9,1,13,1,95,1"⟩,
  ⟨15, 118, 1, "1,1,249,1"⟩,
  ⟨14, 118, 0, "0,5,235,1"⟩,
  ⟨13, 118, 0, "3,2,188,1"⟩,
  ⟨12, 118, 0, "7,1,188,1"⟩,
  ⟨12, 118, 1, "3,2,189,1"⟩,
  ⟨11, 118, 0, "1,1,3,1,213,1"⟩,
  ⟨11, 118, 1, "1,2,239,1"⟩,
  ⟨11, 118, 2, "0,2,251,1"⟩,
  ⟨10, 118, 0, "1,1,251,1"⟩,
  ⟨10, 118, 1, "0,1,3,1,216,1"⟩,
  ⟨9, 118, 0, "7,1,190,1"⟩,
  ⟨9, 118, 1, "3,2,191,1"⟩,
  ⟨8, 118, 0, "3,1,222,1"⟩,
  ⟨119, 119, 0, "0,119"⟩,
  ⟨40, 119, 0, "0,11,210,1"⟩,
  ⟨38, 119, 0, "0,2,252,1"⟩,
  ⟨37, 119, 0, "0,2,253,1"⟩,
  ⟨34, 119, 0, "0,8,224,1"⟩,
  ⟨33, 119, 0, "0,8,225,1"⟩,
  ⟨28, 119, 0, "0,2,16,1,137,1"⟩,
  ⟨27, 119, 0, "0,2,16,1,138,1"⟩,
  ⟨27, 119, 1, "0,3,244,1"⟩,
  ⟨26, 119, 0, "0,2,17,1,138,1"⟩,
  ⟨25, 119, 0, "0,3,245,1"⟩,
  ⟨24, 119, 1, "0,3,246,1"⟩,
  ⟨23, 119, 0, "0,2,8,2,118,1"⟩,
  ⟨22, 119, 0, "258,1"⟩,
  ⟨21, 119, 0, "259,1"⟩,
  ⟨20, 119, 0, "8,1,180,1"⟩,
  ⟨19, 119, 0, "9,1,167,1"⟩,
  ⟨18, 119, 1, "0,2,254,1"⟩,
  ⟨17, 119, 0, "0,1,50,1,69,1"⟩,
  ⟨17, 119, 1, "0,2,255,1"⟩,
  ⟨14, 119, 0, "0,1,3,2,188,1"⟩,
  ⟨13, 119, 0, "0,1,7,1,188,1"⟩,
  ⟨11, 119, 0, "262,1"⟩,
  ⟨11, 119, 1, "0,2,3,1,216,1"⟩,
  ⟨10, 119, 1, "0,1,3,2,191,1"⟩,
  ⟨8, 119, 0, "53,1,69,1"⟩,
  ⟨7, 119, 0, "264,1"⟩,
  ⟨120, 120, 0, "0,120"⟩,
  ⟨39, 120, 0, "0,3,252,1"⟩,
  ⟨35, 120, 0, "8,1,183,1"⟩,
  ⟨32, 120, 0, "8,3,71,1"⟩,
  ⟨31, 120, 0, "8,2,16,1,50,1"⟩,
  ⟨30, 120, 0, "8,2,17,1,50,1"⟩,
  ⟨29, 120, 0, "8,2,125,1"⟩,
  ⟨28, 120, 0, "8,5,16,1"⟩,
  ⟨28, 120, 1, "0,4,244,1"⟩,
  ⟨27, 120, 0, "8,5,17,1"⟩,
  ⟨27, 120, 1, "0,3,17,1,138,1"⟩,
  ⟨26, 120, 1, "8,3,16,1,23,1"⟩,
  ⟨26, 120, 3, "0,4,245,1"⟩,
  ⟨25, 120, 0, "8,1,185,1"⟩,
  ⟨25, 120, 1, "8,4,42,1"⟩,
  ⟨25, 120, 2, "0,1,257,1"⟩,
  ⟨25, 120, 3, "0,4,246,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1857_mem, Shared.BasisChunk001.row1858_mem, Shared.BasisChunk001.row1860_mem, Shared.BasisChunk001.row1861_mem, Shared.BasisChunk001.row1863_mem, Shared.BasisChunk001.row1864_mem, Shared.BasisChunk001.row1865_mem, Shared.BasisChunk001.row1866_mem, Shared.BasisChunk001.row1867_mem, Shared.BasisChunk001.row1868_mem, Shared.BasisChunk001.row1869_mem, Shared.BasisChunk001.row1870_mem, Shared.BasisChunk001.row1872_mem, Shared.BasisChunk001.row1873_mem, Shared.BasisChunk001.row1874_mem, Shared.BasisChunk001.row1875_mem, Shared.BasisChunk001.row1876_mem, Shared.BasisChunk001.row1877_mem, Shared.BasisChunk001.row1878_mem, Shared.BasisChunk001.row1879_mem, Shared.BasisChunk001.row1880_mem, Shared.BasisChunk001.row1881_mem, Shared.BasisChunk001.row1882_mem, Shared.BasisChunk001.row1883_mem, Shared.BasisChunk001.row1885_mem, Shared.BasisChunk001.row1886_mem, Shared.BasisChunk001.row1887_mem, Shared.BasisChunk001.row1888_mem, Shared.BasisChunk001.row1889_mem, Shared.BasisChunk001.row1890_mem, Shared.BasisChunk001.row1891_mem, Shared.BasisChunk001.row1892_mem, Shared.BasisChunk001.row1893_mem, Shared.BasisChunk001.row1895_mem, Shared.BasisChunk001.row1896_mem, Shared.BasisChunk001.row1897_mem, Shared.BasisChunk001.row1898_mem, Shared.BasisChunk001.row1899_mem, Shared.BasisChunk001.row1900_mem, Shared.BasisChunk001.row1902_mem, Shared.BasisChunk001.row1903_mem, Shared.BasisChunk001.row1904_mem, Shared.BasisChunk001.row1905_mem, Shared.BasisChunk001.row1906_mem, Shared.BasisChunk001.row1908_mem, Shared.BasisChunk001.row1909_mem, Shared.BasisChunk001.row1911_mem, Shared.BasisChunk001.row1913_mem, Shared.BasisChunk001.row1914_mem, Shared.BasisChunk001.row1915_mem, Shared.BasisChunk001.row1916_mem, Shared.BasisChunk001.row1918_mem, Shared.BasisChunk001.row1920_mem, Shared.BasisChunk001.row1921_mem, Shared.BasisChunk001.row1922_mem, Shared.BasisChunk001.row1923_mem, Shared.BasisChunk001.row1924_mem, Shared.BasisChunk001.row1925_mem, Shared.BasisChunk001.row1926_mem, Shared.BasisChunk001.row1927_mem, Shared.BasisChunk001.row1929_mem, Shared.BasisChunk001.row1931_mem, Shared.BasisChunk001.row1932_mem, Shared.BasisChunk001.row1933_mem, Shared.BasisChunk001.row1934_mem, Shared.BasisChunk001.row1935_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard024
