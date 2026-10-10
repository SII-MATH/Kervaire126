import KIP126.LinProgram.Generated.Naturality.Words200.Shard027
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard027
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard027
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
  exact ⟨Shared.RelationChunk002.relation244_zero, Shared.RelationChunk006.relation381_zero, Shared.RelationChunk006.relation382_zero, Shared.RelationChunk006.relation383_zero, Shared.RelationChunk006.relation384_zero, Shared.RelationChunk006.relation386_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3458 128 := by cbv
private def targetRows : List BasisRow := [⟨35, 124, 0, "0,1,17,1,153,1"⟩,
  ⟨30, 124, 0, "0,8,245,1"⟩,
  ⟨29, 124, 0, "0,8,246,1"⟩,
  ⟨27, 124, 0, "0,1,8,2,137,1"⟩,
  ⟨26, 124, 0, "0,1,8,2,138,1"⟩,
  ⟨26, 124, 1, "0,2,16,1,149,1"⟩,
  ⟨25, 124, 0, "0,1,16,1,154,1"⟩,
  ⟨25, 124, 1, "0,2,17,1,149,1"⟩,
  ⟨24, 124, 0, "0,1,17,1,154,1"⟩,
  ⟨23, 124, 0, "0,5,260,1"⟩,
  ⟨22, 124, 0, "0,3,274,1"⟩,
  ⟨20, 124, 0, "0,2,278,1"⟩,
  ⟨19, 124, 0, "1,1,278,1"⟩,
  ⟨17, 124, 0, "13,2,105,1"⟩,
  ⟨17, 124, 1, "0,1,8,1,201,1"⟩,
  ⟨16, 124, 0, "9,1,23,1,75,1"⟩,
  ⟨16, 124, 1, "0,1,284,1"⟩,
  ⟨16, 124, 2, "0,1,9,1,188,1"⟩,
  ⟨15, 124, 0, "1,1,279,1"⟩,
  ⟨15, 124, 1, "0,1,286,1"⟩,
  ⟨15, 124, 2, "0,1,285,1"⟩,
  ⟨14, 124, 0, "59,1,69,1"⟩,
  ⟨14, 124, 1, "2,1,268,1"⟩,
  ⟨14, 124, 2, "1,1,280,1"⟩,
  ⟨13, 124, 0, "0,4,270,1"⟩,
  ⟨12, 124, 0, "0,1,7,1,209,1"⟩,
  ⟨11, 124, 0, "1,1,281,1"⟩,
  ⟨11, 124, 1, "1,2,270,1"⟩,
  ⟨10, 124, 0, "2,1,270,1"⟩,
  ⟨10, 124, 1, "1,1,282,1"⟩,
  ⟨9, 124, 0, "2,1,272,1"⟩,
  ⟨8, 124, 0, "2,1,54,1,69,1"⟩,
  ⟨7, 124, 0, "2,1,273,1"⟩,
  ⟨125, 125, 0, "0,125"⟩,
  ⟨42, 125, 0, "0,1,290,1"⟩,
  ⟨38, 125, 0, "0,2,8,1,199,1"⟩,
  ⟨37, 125, 0, "0,2,8,1,200,1"⟩,
  ⟨31, 125, 1, "0,9,245,1"⟩,
  ⟨30, 125, 0, "0,9,246,1"⟩,
  ⟨28, 125, 0, "0,2,8,2,137,1"⟩,
  ⟨27, 125, 0, "0,2,8,2,138,1"⟩,
  ⟨26, 125, 0, "0,3,17,1,149,1"⟩,
  ⟨25, 125, 0, "0,2,17,1,154,1"⟩,
  ⟨24, 125, 2, "0,6,260,1"⟩,
  ⟨23, 125, 0, "17,1,160,1"⟩,
  ⟨23, 125, 1, "0,4,274,1"⟩,
  ⟨22, 125, 0, "8,1,207,1"⟩,
  ⟨21, 125, 0, "8,1,208,1"⟩,
  ⟨21, 125, 1, "0,3,278,1"⟩,
  ⟨20, 125, 0, "9,1,194,1"⟩,
  ⟨18, 125, 1, "0,2,8,1,201,1"⟩,
  ⟨17, 125, 0, "292,1"⟩,
  ⟨17, 125, 1, "0,2,284,1"⟩,
  ⟨17, 125, 2, "0,2,9,1,188,1"⟩,
  ⟨16, 125, 0, "0,2,285,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2093_mem, Shared.BasisChunk002.row2094_mem, Shared.BasisChunk002.row2095_mem, Shared.BasisChunk002.row2096_mem, Shared.BasisChunk002.row2097_mem, Shared.BasisChunk002.row2098_mem, Shared.BasisChunk002.row2099_mem, Shared.BasisChunk002.row2100_mem, Shared.BasisChunk002.row2101_mem, Shared.BasisChunk002.row2102_mem, Shared.BasisChunk002.row2103_mem, Shared.BasisChunk002.row2104_mem, Shared.BasisChunk002.row2105_mem, Shared.BasisChunk002.row2106_mem, Shared.BasisChunk002.row2107_mem, Shared.BasisChunk002.row2108_mem, Shared.BasisChunk002.row2109_mem, Shared.BasisChunk002.row2110_mem, Shared.BasisChunk002.row2111_mem, Shared.BasisChunk002.row2112_mem, Shared.BasisChunk002.row2113_mem, Shared.BasisChunk002.row2114_mem, Shared.BasisChunk002.row2115_mem, Shared.BasisChunk002.row2116_mem, Shared.BasisChunk002.row2117_mem, Shared.BasisChunk002.row2118_mem, Shared.BasisChunk002.row2119_mem, Shared.BasisChunk002.row2120_mem, Shared.BasisChunk002.row2121_mem, Shared.BasisChunk002.row2122_mem, Shared.BasisChunk002.row2123_mem, Shared.BasisChunk002.row2124_mem, Shared.BasisChunk002.row2125_mem, Shared.BasisChunk002.row2126_mem, Shared.BasisChunk002.row2127_mem, Shared.BasisChunk002.row2128_mem, Shared.BasisChunk002.row2129_mem, Shared.BasisChunk002.row2131_mem, Shared.BasisChunk002.row2132_mem, Shared.BasisChunk002.row2133_mem, Shared.BasisChunk002.row2134_mem, Shared.BasisChunk002.row2135_mem, Shared.BasisChunk002.row2136_mem, Shared.BasisChunk002.row2139_mem, Shared.BasisChunk002.row2140_mem, Shared.BasisChunk002.row2141_mem, Shared.BasisChunk002.row2142_mem, Shared.BasisChunk002.row2143_mem, Shared.BasisChunk002.row2144_mem, Shared.BasisChunk002.row2145_mem, Shared.BasisChunk002.row2147_mem, Shared.BasisChunk002.row2148_mem, Shared.BasisChunk002.row2149_mem, Shared.BasisChunk002.row2150_mem, Shared.BasisChunk002.row2151_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard027
