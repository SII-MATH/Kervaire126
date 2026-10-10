import KIP126.LinProgram.Generated.Naturality.Words200.Shard038
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard038
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard038
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation26_zero, Shared.RelationChunk000.relation29_zero, Shared.RelationChunk000.relation36_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation131_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation171_zero, Shared.RelationChunk001.relation193_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk001.relation198_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk002.relation251_zero, Shared.RelationChunk003.relation252_zero, Shared.RelationChunk003.relation255_zero, Shared.RelationChunk004.relation314_zero, Shared.RelationChunk005.relation348_zero, Shared.RelationChunk005.relation349_zero, Shared.RelationChunk005.relation350_zero, Shared.RelationChunk005.relation351_zero, Shared.RelationChunk005.relation352_zero, Shared.RelationChunk005.relation353_zero, Shared.RelationChunk005.relation356_zero, Shared.RelationChunk009.relation487_zero, Shared.RelationChunk009.relation505_zero, Shared.RelationChunk009.relation506_zero, Shared.RelationChunk009.relation507_zero, Shared.RelationChunk009.relation508_zero, Shared.RelationChunk009.relation518_zero, Shared.RelationChunk009.relation519_zero, Shared.RelationChunk009.relation520_zero, Shared.RelationChunk010.relation525_zero, Shared.RelationChunk010.relation526_zero, Shared.RelationChunk010.relation527_zero, Shared.RelationChunk010.relation528_zero, Shared.RelationChunk010.relation529_zero, Shared.RelationChunk010.relation530_zero, Shared.RelationChunk010.relation531_zero, Shared.RelationChunk010.relation532_zero, Shared.RelationChunk010.relation533_zero, Shared.RelationChunk010.relation535_zero, Shared.RelationChunk010.relation536_zero, Shared.RelationChunk010.relation537_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4866 128 := by cbv
private def targetRows : List BasisRow := [⟨18, 137, 1, "0,1,2,1,359,1"⟩,
  ⟨17, 137, 1, "17,1,209,1"⟩,
  ⟨17, 137, 2, "0,1,3,2,267,1"⟩,
  ⟨16, 137, 0, "422,1"⟩,
  ⟨16, 137, 1, "8,1,261,1"⟩,
  ⟨16, 137, 2, "0,1,7,1,267,1"⟩,
  ⟨15, 137, 1, "423,1"⟩,
  ⟨14, 137, 0, "23,1,181,1"⟩,
  ⟨14, 137, 1, "0,1,418,1"⟩,
  ⟨14, 137, 2, "0,3,386,1"⟩,
  ⟨13, 137, 0, "76,1,82,1"⟩,
  ⟨13, 137, 1, "9,1,251,1"⟩,
  ⟨13, 137, 3, "0,5,367,1"⟩,
  ⟨12, 137, 2, "0,1,69,1,89,1"⟩,
  ⟨12, 137, 3, "0,3,391,1"⟩,
  ⟨12, 137, 4, "0,4,375,1"⟩,
  ⟨11, 137, 1, "1,1,413,1"⟩,
  ⟨11, 137, 2, "1,1,412,1"⟩,
  ⟨11, 137, 3, "0,1,419,1"⟩,
  ⟨11, 137, 4, "0,2,414,1"⟩,
  ⟨11, 137, 5, "0,9,69,2"⟩,
  ⟨10, 137, 1, "3,1,333,1"⟩,
  ⟨10, 137, 2, "2,1,373,1"⟩,
  ⟨10, 137, 3, "1,2,375,1"⟩,
  ⟨10, 137, 4, "0,2,415,1"⟩,
  ⟨10, 137, 5, "0,9,324,1"⟩,
  ⟨9, 137, 0, "2,1,376,1"⟩,
  ⟨9, 137, 2, "0,1,3,1,68,1,69,1"⟩,
  ⟨8, 137, 0, "429,1"⟩,
  ⟨4, 137, 0, "0,1,3,1,69,2"⟩,
  ⟨3, 137, 0, "0,1,3,1,324,1"⟩,
  ⟨138, 138, 0, "0,138"⟩,
  ⟨47, 138, 0, "0,2,416,1"⟩,
  ⟨43, 138, 0, "0,22,246,1"⟩,
  ⟨39, 138, 0, "8,2,183,1"⟩,
  ⟨38, 138, 0, "16,1,17,1,111,1"⟩,
  ⟨37, 138, 0, "8,1,265,1"⟩,
  ⟨37, 138, 1, "0,3,402,1"⟩,
  ⟨36, 138, 0, "8,4,71,1"⟩,
  ⟨36, 138, 1, "0,3,403,1"⟩,
  ⟨35, 138, 0, "8,3,16,1,50,1"⟩,
  ⟨34, 138, 1, "8,3,17,1,50,1"⟩,
  ⟨33, 138, 0, "433,1"⟩,
  ⟨33, 138, 1, "8,3,125,1"⟩,
  ⟨32, 138, 0, "8,6,16,1"⟩,
  ⟨31, 138, 0, "8,6,17,1"⟩,
  ⟨30, 138, 1, "8,4,16,1,23,1"⟩,
  ⟨29, 138, 0, "8,2,185,1"⟩,
  ⟨29, 138, 1, "8,5,42,1"⟩,
  ⟨29, 138, 2, "0,12,300,1"⟩,
  ⟨28, 138, 0, "8,1,17,1,147,1"⟩,
  ⟨28, 138, 1, "8,5,13,2"⟩,
  ⟨28, 138, 2, "0,10,317,1"⟩,
  ⟨27, 138, 0, "17,2,113,1"⟩,
  ⟨27, 138, 1, "8,4,13,1,32,1"⟩,
  ⟨26, 138, 0, "8,3,13,2,23,1"⟩,
  ⟨26, 138, 1, "8,4,72,1"⟩,
  ⟨25, 138, 0, "8,2,13,2,51,1"⟩,
  ⟨25, 138, 1, "8,3,127,1"⟩,
  ⟨24, 138, 0, "8,1,13,5"⟩,
  ⟨24, 138, 1, "8,2,20,1,80,1"⟩,
  ⟨23, 138, 0, "13,4,32,1"⟩,
  ⟨23, 138, 1, "8,2,186,1"⟩,
  ⟨23, 138, 2, "0,1,8,1,260,1"⟩,
  ⟨22, 138, 0, "434,1"⟩,
  ⟨22, 138, 1, "13,4,33,1"⟩,
  ⟨22, 138, 2, "8,1,9,1,13,1,101,1"⟩,
  ⟨21, 138, 1, "9,1,13,2,80,1"⟩,
  ⟨20, 138, 1, "2,1,381,1"⟩,
  ⟨19, 138, 0, "8,2,188,1"⟩,
  ⟨19, 138, 2, "0,1,16,1,209,1"⟩,
  ⟨18, 138, 0, "22,1,188,1"⟩,
  ⟨18, 138, 1, "8,1,267,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2902_mem, Shared.BasisChunk002.row2904_mem, Shared.BasisChunk002.row2905_mem, Shared.BasisChunk002.row2906_mem, Shared.BasisChunk002.row2907_mem, Shared.BasisChunk002.row2908_mem, Shared.BasisChunk002.row2910_mem, Shared.BasisChunk002.row2911_mem, Shared.BasisChunk002.row2912_mem, Shared.BasisChunk002.row2913_mem, Shared.BasisChunk002.row2914_mem, Shared.BasisChunk002.row2915_mem, Shared.BasisChunk002.row2917_mem, Shared.BasisChunk002.row2920_mem, Shared.BasisChunk002.row2921_mem, Shared.BasisChunk002.row2922_mem, Shared.BasisChunk002.row2924_mem, Shared.BasisChunk002.row2925_mem, Shared.BasisChunk002.row2926_mem, Shared.BasisChunk002.row2927_mem, Shared.BasisChunk002.row2928_mem, Shared.BasisChunk002.row2930_mem, Shared.BasisChunk002.row2931_mem, Shared.BasisChunk002.row2932_mem, Shared.BasisChunk002.row2933_mem, Shared.BasisChunk002.row2934_mem, Shared.BasisChunk002.row2935_mem, Shared.BasisChunk002.row2937_mem, Shared.BasisChunk002.row2938_mem, Shared.BasisChunk002.row2941_mem, Shared.BasisChunk002.row2942_mem, Shared.BasisChunk002.row2943_mem, Shared.BasisChunk002.row2944_mem, Shared.BasisChunk002.row2946_mem, Shared.BasisChunk002.row2948_mem, Shared.BasisChunk002.row2949_mem, Shared.BasisChunk002.row2950_mem, Shared.BasisChunk002.row2951_mem, Shared.BasisChunk002.row2952_mem, Shared.BasisChunk002.row2953_mem, Shared.BasisChunk002.row2954_mem, Shared.BasisChunk002.row2956_mem, Shared.BasisChunk002.row2957_mem, Shared.BasisChunk002.row2958_mem, Shared.BasisChunk002.row2959_mem, Shared.BasisChunk002.row2960_mem, Shared.BasisChunk002.row2962_mem, Shared.BasisChunk002.row2963_mem, Shared.BasisChunk002.row2964_mem, Shared.BasisChunk002.row2965_mem, Shared.BasisChunk002.row2966_mem, Shared.BasisChunk002.row2967_mem, Shared.BasisChunk002.row2968_mem, Shared.BasisChunk002.row2969_mem, Shared.BasisChunk002.row2970_mem, Shared.BasisChunk002.row2971_mem, Shared.BasisChunk002.row2972_mem, Shared.BasisChunk002.row2973_mem, Shared.BasisChunk002.row2974_mem, Shared.BasisChunk002.row2975_mem, Shared.BasisChunk002.row2976_mem, Shared.BasisChunk002.row2977_mem, Shared.BasisChunk002.row2978_mem, Shared.BasisChunk002.row2979_mem, Shared.BasisChunk002.row2980_mem, Shared.BasisChunk002.row2981_mem, Shared.BasisChunk002.row2982_mem, Shared.BasisChunk002.row2984_mem, Shared.BasisChunk002.row2986_mem, Shared.BasisChunk002.row2987_mem, Shared.BasisChunk002.row2989_mem, Shared.BasisChunk002.row2990_mem, Shared.BasisChunk002.row2991_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard038
