import KIP126.LinProgram.Generated.Naturality.Words200.Shard026
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard026
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard026
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation182_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, Shared.RelationChunk001.relation187_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation272_zero, Shared.RelationChunk003.relation274_zero, Shared.RelationChunk003.relation275_zero, Shared.RelationChunk006.relation370_zero, Shared.RelationChunk006.relation371_zero, Shared.RelationChunk006.relation372_zero, Shared.RelationChunk006.relation373_zero, Shared.RelationChunk006.relation374_zero, Shared.RelationChunk006.relation375_zero, Shared.RelationChunk006.relation377_zero, Shared.RelationChunk006.relation378_zero, Shared.RelationChunk006.relation379_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3330 128 := by cbv
private def targetRows : List BasisRow := [⟨38, 122, 0, "0,2,8,1,182,1"⟩,
  ⟨37, 122, 0, "0,2,8,1,183,1"⟩,
  ⟨30, 122, 0, "0,6,244,1"⟩,
  ⟨29, 122, 0, "0,5,17,1,138,1"⟩,
  ⟨28, 122, 0, "0,2,8,1,184,1"⟩,
  ⟨28, 122, 1, "0,6,245,1"⟩,
  ⟨27, 122, 0, "0,2,8,1,185,1"⟩,
  ⟨27, 122, 1, "0,3,257,1"⟩,
  ⟨27, 122, 2, "0,6,246,1"⟩,
  ⟨23, 122, 0, "17,1,149,1"⟩,
  ⟨22, 122, 0, "277,1"⟩,
  ⟨21, 122, 0, "8,1,193,1"⟩,
  ⟨21, 122, 1, "0,3,260,1"⟩,
  ⟨20, 122, 0, "8,1,194,1"⟩,
  ⟨20, 122, 1, "0,1,274,1"⟩,
  ⟨19, 122, 0, "13,1,167,1"⟩,
  ⟨18, 122, 1, "13,1,168,1"⟩,
  ⟨18, 122, 2, "0,2,8,1,187,1"⟩,
  ⟨17, 122, 0, "0,1,56,1,69,1"⟩,
  ⟨17, 122, 1, "0,2,266,1"⟩,
  ⟨17, 122, 2, "0,2,8,1,188,1"⟩,
  ⟨16, 122, 0, "0,2,267,1"⟩,
  ⟨11, 122, 1, "0,2,270,1"⟩,
  ⟨123, 123, 0, "0,123"⟩,
  ⟨35, 123, 0, "8,1,200,1"⟩,
  ⟨34, 123, 0, "17,1,153,1"⟩,
  ⟨33, 123, 0, "283,1"⟩,
  ⟨32, 123, 0, "8,3,77,1"⟩,
  ⟨31, 123, 0, "8,3,78,1"⟩,
  ⟨30, 123, 0, "8,2,17,1,56,1"⟩,
  ⟨29, 123, 0, "8,2,136,1"⟩,
  ⟨29, 123, 1, "0,7,245,1"⟩,
  ⟨28, 123, 0, "8,5,19,1"⟩,
  ⟨28, 123, 1, "0,7,246,1"⟩,
  ⟨27, 123, 0, "8,5,20,1"⟩,
  ⟨26, 123, 1, "8,4,45,1"⟩,
  ⟨25, 123, 0, "8,2,138,1"⟩,
  ⟨25, 123, 1, "8,4,46,1"⟩,
  ⟨25, 123, 2, "0,1,16,1,149,1"⟩,
  ⟨24, 123, 0, "16,1,154,1"⟩,
  ⟨24, 123, 1, "8,3,9,1,13,2"⟩,
  ⟨24, 123, 2, "0,1,17,1,149,1"⟩,
  ⟨23, 123, 1, "17,1,154,1"⟩,
  ⟨23, 123, 2, "8,2,9,1,13,1,32,1"⟩,
  ⟨22, 123, 0, "8,1,9,1,13,2,23,1"⟩,
  ⟨22, 123, 1, "8,3,79,1"⟩,
  ⟨22, 123, 2, "0,4,260,1"⟩,
  ⟨21, 123, 0, "9,1,13,2,51,1"⟩,
  ⟨21, 123, 1, "8,3,80,1"⟩,
  ⟨21, 123, 2, "0,2,274,1"⟩,
  ⟨20, 123, 0, "8,1,22,1,80,1"⟩,
  ⟨19, 123, 0, "8,1,23,1,80,1"⟩,
  ⟨19, 123, 1, "0,1,278,1"⟩,
  ⟨18, 123, 0, "13,2,101,1"⟩,
  ⟨18, 123, 1, "0,2,56,1,69,1"⟩,
  ⟨16, 123, 1, "1,1,5,1,209,1"⟩,
  ⟨15, 123, 1, "9,1,188,1"⟩,
  ⟨14, 123, 0, "286,1"⟩,
  ⟨14, 123, 1, "285,1"⟩,
  ⟨13, 123, 1, "1,1,275,1"⟩,
  ⟨12, 123, 0, "2,1,262,1"⟩,
  ⟨12, 123, 1, "0,3,270,1"⟩,
  ⟨11, 123, 0, "7,1,209,1"⟩,
  ⟨11, 123, 1, "0,1,281,1"⟩,
  ⟨10, 123, 0, "288,1"⟩,
  ⟨9, 123, 1, "2,1,53,1,69,1"⟩,
  ⟨8, 123, 0, "2,1,264,1"⟩,
  ⟨124, 124, 0, "0,124"⟩,
  ⟨41, 124, 0, "290,1"⟩,
  ⟨37, 124, 0, "0,1,8,1,199,1"⟩,
  ⟨36, 124, 0, "0,1,8,1,200,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row2004_mem, Shared.BasisChunk001.row2005_mem, Shared.BasisChunk001.row2007_mem, Shared.BasisChunk001.row2008_mem, Shared.BasisChunk001.row2009_mem, Shared.BasisChunk001.row2010_mem, Shared.BasisChunk001.row2011_mem, Shared.BasisChunk001.row2012_mem, Shared.BasisChunk001.row2013_mem, Shared.BasisChunk001.row2015_mem, Shared.BasisChunk001.row2016_mem, Shared.BasisChunk001.row2017_mem, Shared.BasisChunk001.row2018_mem, Shared.BasisChunk001.row2019_mem, Shared.BasisChunk001.row2020_mem, Shared.BasisChunk001.row2021_mem, Shared.BasisChunk001.row2023_mem, Shared.BasisChunk001.row2024_mem, Shared.BasisChunk001.row2025_mem, Shared.BasisChunk001.row2026_mem, Shared.BasisChunk001.row2027_mem, Shared.BasisChunk001.row2028_mem, Shared.BasisChunk001.row2032_mem, Shared.BasisChunk001.row2036_mem, Shared.BasisChunk001.row2038_mem, Shared.BasisChunk001.row2039_mem, Shared.BasisChunk001.row2040_mem, Shared.BasisChunk001.row2041_mem, Shared.BasisChunk001.row2042_mem, Shared.BasisChunk001.row2043_mem, Shared.BasisChunk001.row2044_mem, Shared.BasisChunk001.row2045_mem, Shared.BasisChunk001.row2046_mem, Shared.BasisChunk001.row2047_mem, Shared.BasisChunk002.row2048_mem, Shared.BasisChunk002.row2050_mem, Shared.BasisChunk002.row2051_mem, Shared.BasisChunk002.row2052_mem, Shared.BasisChunk002.row2053_mem, Shared.BasisChunk002.row2054_mem, Shared.BasisChunk002.row2055_mem, Shared.BasisChunk002.row2056_mem, Shared.BasisChunk002.row2058_mem, Shared.BasisChunk002.row2059_mem, Shared.BasisChunk002.row2060_mem, Shared.BasisChunk002.row2061_mem, Shared.BasisChunk002.row2062_mem, Shared.BasisChunk002.row2063_mem, Shared.BasisChunk002.row2064_mem, Shared.BasisChunk002.row2065_mem, Shared.BasisChunk002.row2066_mem, Shared.BasisChunk002.row2068_mem, Shared.BasisChunk002.row2069_mem, Shared.BasisChunk002.row2070_mem, Shared.BasisChunk002.row2071_mem, Shared.BasisChunk002.row2073_mem, Shared.BasisChunk002.row2075_mem, Shared.BasisChunk002.row2076_mem, Shared.BasisChunk002.row2077_mem, Shared.BasisChunk002.row2079_mem, Shared.BasisChunk002.row2080_mem, Shared.BasisChunk002.row2081_mem, Shared.BasisChunk002.row2082_mem, Shared.BasisChunk002.row2083_mem, Shared.BasisChunk002.row2084_mem, Shared.BasisChunk002.row2086_mem, Shared.BasisChunk002.row2087_mem, Shared.BasisChunk002.row2088_mem, Shared.BasisChunk002.row2090_mem, Shared.BasisChunk002.row2091_mem, Shared.BasisChunk002.row2092_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard026
