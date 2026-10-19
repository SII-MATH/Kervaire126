module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard041
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard041
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard041
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
  exact ⟨Shared.RelationChunk000.relation3_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation181_zero, Shared.RelationChunk001.relation182_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation272_zero, Shared.RelationChunk003.relation274_zero, Shared.RelationChunk003.relation275_zero, Shared.RelationChunk006.relation370_zero, Shared.RelationChunk006.relation371_zero, Shared.RelationChunk006.relation372_zero, Shared.RelationChunk006.relation377_zero, Shared.RelationChunk006.relation378_zero, Shared.RelationChunk006.relation379_zero, Shared.RelationChunk010.relation543_zero, Shared.RelationChunk010.relation544_zero, Shared.RelationChunk010.relation545_zero, Shared.RelationChunk010.relation546_zero, Shared.RelationChunk010.relation547_zero, Shared.RelationChunk010.relation548_zero, Shared.RelationChunk010.relation562_zero, Shared.RelationChunk010.relation563_zero, Shared.RelationChunk010.relation564_zero, Shared.RelationChunk010.relation565_zero, Shared.RelationChunk010.relation566_zero, Shared.RelationChunk011.relation582_zero, Shared.RelationChunk011.relation583_zero, Shared.RelationChunk011.relation584_zero, Shared.RelationChunk011.relation585_zero, Shared.RelationChunk011.relation586_zero, Shared.RelationChunk011.relation587_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5250 128 := by cbv
private def targetRows : List BasisRow := [⟨19, 140, 0, "0,3,422,1"⟩,
  ⟨18, 140, 2, "0,2,437,1"⟩,
  ⟨17, 140, 0, "8,1,280,1"⟩,
  ⟨17, 140, 2, "0,2,438,1"⟩,
  ⟨17, 140, 3, "0,4,418,1"⟩,
  ⟨16, 140, 0, "9,1,261,1"⟩,
  ⟨16, 140, 2, "0,1,448,1"⟩,
  ⟨16, 140, 3, "0,2,440,1"⟩,
  ⟨16, 140, 4, "0,2,439,1"⟩,
  ⟨15, 140, 0, "456,1"⟩,
  ⟨15, 140, 3, "0,1,449,1"⟩,
  ⟨15, 140, 4, "0,3,425,1"⟩,
  ⟨14, 140, 1, "68,1,107,1"⟩,
  ⟨14, 140, 2, "1,1,3,1,335,1"⟩,
  ⟨14, 140, 3, "0,12,69,2"⟩,
  ⟨13, 140, 1, "13,1,251,1"⟩,
  ⟨13, 140, 2, "3,1,363,1"⟩,
  ⟨13, 140, 3, "0,3,428,1"⟩,
  ⟨13, 140, 4, "0,12,324,1"⟩,
  ⟨12, 140, 0, "460,1"⟩,
  ⟨12, 140, 2, "76,1,95,1"⟩,
  ⟨12, 140, 3, "3,1,365,1"⟩,
  ⟨12, 140, 4, "0,1,18,1,209,1"⟩,
  ⟨11, 140, 0, "462,1"⟩,
  ⟨11, 140, 1, "461,1"⟩,
  ⟨11, 140, 2, "69,1,104,1"⟩,
  ⟨11, 140, 4, "0,1,450,1"⟩,
  ⟨11, 140, 5, "0,2,443,1"⟩,
  ⟨10, 140, 0, "463,1"⟩,
  ⟨10, 140, 1, "18,1,213,1"⟩,
  ⟨10, 140, 2, "3,1,366,1"⟩,
  ⟨10, 140, 3, "0,1,3,1,352,1"⟩,
  ⟨10, 140, 4, "0,2,445,1"⟩,
  ⟨9, 140, 0, "464,1"⟩,
  ⟨9, 140, 2, "3,1,367,1"⟩,
  ⟨9, 140, 3, "1,1,445,1"⟩,
  ⟨9, 140, 4, "0,1,451,1"⟩,
  ⟨8, 140, 0, "466,1"⟩,
  ⟨8, 140, 1, "465,1"⟩,
  ⟨8, 140, 2, "2,2,368,1"⟩,
  ⟨8, 140, 3, "0,2,446,1"⟩,
  ⟨8, 140, 4, "0,2,3,1,340,1"⟩,
  ⟨7, 140, 0, "467,1"⟩,
  ⟨7, 140, 1, "3,1,368,1"⟩,
  ⟨7, 140, 2, "1,1,446,1"⟩,
  ⟨5, 140, 0, "1,2,3,1,69,2"⟩,
  ⟨4, 140, 0, "1,2,3,1,324,1"⟩,
  ⟨141, 141, 0, "0,141"⟩,
  ⟨46, 141, 0, "0,25,246,1"⟩,
  ⟨43, 141, 0, "470,1"⟩,
  ⟨40, 141, 1, "0,6,402,1"⟩,
  ⟨39, 141, 0, "8,2,200,1"⟩,
  ⟨39, 141, 1, "0,6,403,1"⟩,
  ⟨38, 141, 0, "8,1,17,1,153,1"⟩,
  ⟨37, 141, 0, "8,1,283,1"⟩,
  ⟨37, 141, 1, "0,3,432,1"⟩,
  ⟨36, 141, 0, "8,4,77,1"⟩,
  ⟨35, 141, 0, "8,4,78,1"⟩,
  ⟨34, 141, 1, "8,3,17,1,56,1"⟩,
  ⟨33, 141, 0, "16,1,225,1"⟩,
  ⟨33, 141, 1, "8,3,136,1"⟩,
  ⟨33, 141, 2, "0,1,452,1"⟩,
  ⟨32, 141, 0, "17,1,225,1"⟩,
  ⟨32, 141, 1, "8,6,19,1"⟩,
  ⟨31, 141, 0, "8,6,20,1"⟩,
  ⟨30, 141, 1, "8,5,45,1"⟩,
  ⟨29, 141, 0, "8,3,138,1"⟩,
  ⟨29, 141, 1, "8,5,46,1"⟩,
  ⟨28, 141, 0, "8,1,16,1,154,1"⟩,
  ⟨28, 141, 1, "8,4,9,1,13,2"⟩,
  ⟨27, 141, 0, "8,1,17,1,154,1"⟩,
  ⟨27, 141, 1, "8,3,9,1,13,1,32,1"⟩,
  ⟨26, 141, 0, "8,2,9,1,13,2,23,1"⟩,
  ⟨26, 141, 1, "8,4,79,1"⟩,
  ⟨25, 141, 0, "8,1,9,1,13,2,51,1"⟩,
  ⟨25, 141, 1, "8,4,80,1"⟩,
  ⟨24, 141, 1, "9,1,13,5"⟩,
  ⟨24, 141, 2, "8,2,22,1,80,1"⟩,
  ⟨23, 141, 0, "64,1,113,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3137_mem, Shared.BasisChunk003.row3140_mem, Shared.BasisChunk003.row3141_mem, Shared.BasisChunk003.row3143_mem, Shared.BasisChunk003.row3144_mem, Shared.BasisChunk003.row3145_mem, Shared.BasisChunk003.row3147_mem, Shared.BasisChunk003.row3148_mem, Shared.BasisChunk003.row3149_mem, Shared.BasisChunk003.row3150_mem, Shared.BasisChunk003.row3153_mem, Shared.BasisChunk003.row3154_mem, Shared.BasisChunk003.row3156_mem, Shared.BasisChunk003.row3157_mem, Shared.BasisChunk003.row3158_mem, Shared.BasisChunk003.row3160_mem, Shared.BasisChunk003.row3161_mem, Shared.BasisChunk003.row3162_mem, Shared.BasisChunk003.row3163_mem, Shared.BasisChunk003.row3164_mem, Shared.BasisChunk003.row3166_mem, Shared.BasisChunk003.row3167_mem, Shared.BasisChunk003.row3168_mem, Shared.BasisChunk003.row3169_mem, Shared.BasisChunk003.row3170_mem, Shared.BasisChunk003.row3171_mem, Shared.BasisChunk003.row3173_mem, Shared.BasisChunk003.row3174_mem, Shared.BasisChunk003.row3175_mem, Shared.BasisChunk003.row3176_mem, Shared.BasisChunk003.row3177_mem, Shared.BasisChunk003.row3178_mem, Shared.BasisChunk003.row3179_mem, Shared.BasisChunk003.row3180_mem, Shared.BasisChunk003.row3182_mem, Shared.BasisChunk003.row3183_mem, Shared.BasisChunk003.row3184_mem, Shared.BasisChunk003.row3185_mem, Shared.BasisChunk003.row3186_mem, Shared.BasisChunk003.row3187_mem, Shared.BasisChunk003.row3188_mem, Shared.BasisChunk003.row3189_mem, Shared.BasisChunk003.row3190_mem, Shared.BasisChunk003.row3191_mem, Shared.BasisChunk003.row3192_mem, Shared.BasisChunk003.row3194_mem, Shared.BasisChunk003.row3195_mem, Shared.BasisChunk003.row3196_mem, Shared.BasisChunk003.row3197_mem, Shared.BasisChunk003.row3199_mem, Shared.BasisChunk003.row3201_mem, Shared.BasisChunk003.row3202_mem, Shared.BasisChunk003.row3203_mem, Shared.BasisChunk003.row3204_mem, Shared.BasisChunk003.row3205_mem, Shared.BasisChunk003.row3206_mem, Shared.BasisChunk003.row3207_mem, Shared.BasisChunk003.row3208_mem, Shared.BasisChunk003.row3210_mem, Shared.BasisChunk003.row3211_mem, Shared.BasisChunk003.row3212_mem, Shared.BasisChunk003.row3213_mem, Shared.BasisChunk003.row3214_mem, Shared.BasisChunk003.row3215_mem, Shared.BasisChunk003.row3216_mem, Shared.BasisChunk003.row3218_mem, Shared.BasisChunk003.row3219_mem, Shared.BasisChunk003.row3220_mem, Shared.BasisChunk003.row3221_mem, Shared.BasisChunk003.row3222_mem, Shared.BasisChunk003.row3223_mem, Shared.BasisChunk003.row3224_mem, Shared.BasisChunk003.row3225_mem, Shared.BasisChunk003.row3226_mem, Shared.BasisChunk003.row3227_mem, Shared.BasisChunk003.row3228_mem, Shared.BasisChunk003.row3230_mem, Shared.BasisChunk003.row3231_mem, Shared.BasisChunk003.row3232_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard041
