import KIP126.LinProgram.Generated.Naturality.Words200.Shard043
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard043
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard043
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
  exact ⟨Shared.RelationChunk000.relation112_zero, Shared.RelationChunk000.relation113_zero, Shared.RelationChunk000.relation116_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk001.relation141_zero, Shared.RelationChunk005.relation361_zero, Shared.RelationChunk011.relation588_zero, Shared.RelationChunk011.relation589_zero, Shared.RelationChunk011.relation590_zero, Shared.RelationChunk011.relation591_zero, Shared.RelationChunk011.relation592_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5506 128 := by cbv
private def targetRows : List BasisRow := [⟨26, 142, 0, "1,1,5,1,64,2"⟩,
  ⟨25, 142, 0, "0,1,64,1,112,1"⟩,
  ⟨24, 142, 0, "0,1,64,1,113,1"⟩,
  ⟨24, 142, 1, "0,2,8,1,278,1"⟩,
  ⟨23, 142, 0, "0,1,471,1"⟩,
  ⟨23, 142, 1, "0,2,454,1"⟩,
  ⟨22, 142, 0, "0,5,17,1,209,1"⟩,
  ⟨21, 142, 0, "0,1,8,2,201,1"⟩,
  ⟨21, 142, 1, "0,5,422,1"⟩,
  ⟨20, 142, 0, "13,3,83,1"⟩,
  ⟨20, 142, 1, "0,1,8,1,9,1,188,1"⟩,
  ⟨20, 142, 2, "0,4,437,1"⟩,
  ⟨19, 142, 0, "9,1,13,2,95,1"⟩,
  ⟨19, 142, 1, "0,1,9,1,267,1"⟩,
  ⟨19, 142, 2, "0,2,3,1,359,1"⟩,
  ⟨19, 142, 3, "0,6,418,1"⟩,
  ⟨18, 142, 0, "0,1,472,1"⟩,
  ⟨18, 142, 1, "0,4,440,1"⟩,
  ⟨17, 142, 0, "0,2,67,1,107,1"⟩,
  ⟨17, 142, 1, "0,3,449,1"⟩,
  ⟨16, 142, 1, "0,2,68,1,107,1"⟩,
  ⟨16, 142, 2, "0,14,69,2"⟩,
  ⟨15, 142, 2, "2,1,439,1"⟩,
  ⟨15, 142, 4, "0,14,324,1"⟩,
  ⟨14, 142, 0, "482,1"⟩,
  ⟨14, 142, 1, "69,1,113,1"⟩,
  ⟨14, 142, 2, "0,1,475,1"⟩,
  ⟨14, 142, 3, "0,2,460,1"⟩,
  ⟨13, 142, 0, "483,1"⟩,
  ⟨13, 142, 1, "1,1,459,1"⟩,
  ⟨12, 142, 2, "1,2,442,1"⟩,
  ⟨11, 142, 3, "0,3,451,1"⟩,
  ⟨10, 142, 0, "3,1,391,1"⟩,
  ⟨10, 142, 1, "3,1,390,1"⟩,
  ⟨10, 142, 2, "0,1,479,1"⟩,
  ⟨10, 142, 3, "0,1,2,1,69,1,95,1"⟩,
  ⟨10, 142, 4, "0,4,446,1"⟩,
  ⟨9, 142, 0, "3,1,394,1"⟩,
  ⟨9, 142, 1, "3,1,392,1"⟩,
  ⟨9, 142, 2, "2,1,445,1"⟩,
  ⟨9, 142, 3, "0,1,480,1"⟩,
  ⟨8, 142, 0, "3,1,397,1"⟩,
  ⟨8, 142, 1, "3,1,396,1"⟩,
  ⟨8, 142, 2, "1,2,446,1"⟩,
  ⟨8, 142, 3, "0,1,3,1,377,1"⟩,
  ⟨7, 142, 1, "3,1,399,1"⟩,
  ⟨7, 142, 2, "3,1,398,1"⟩,
  ⟨7, 142, 3, "0,1,3,1,378,1"⟩,
  ⟨6, 142, 1, "3,1,400,1"⟩,
  ⟨143, 143, 0, "0,143"⟩,
  ⟨48, 143, 0, "0,27,246,1"⟩,
  ⟨46, 143, 0, "0,2,469,1"⟩,
  ⟨45, 143, 0, "0,2,470,1"⟩,
  ⟨42, 143, 0, "0,8,402,1"⟩,
  ⟨41, 143, 0, "0,8,403,1"⟩,
  ⟨36, 143, 0, "0,2,16,1,224,1"⟩,
  ⟨35, 143, 0, "0,2,16,1,225,1"⟩,
  ⟨35, 143, 1, "0,3,452,1"⟩,
  ⟨34, 143, 0, "0,2,17,1,225,1"⟩,
  ⟨31, 143, 0, "0,2,8,3,138,1"⟩,
  ⟨30, 143, 0, "489,1"⟩,
  ⟨29, 143, 0, "490,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3301_mem, Shared.BasisChunk003.row3302_mem, Shared.BasisChunk003.row3303_mem, Shared.BasisChunk003.row3304_mem, Shared.BasisChunk003.row3305_mem, Shared.BasisChunk003.row3306_mem, Shared.BasisChunk003.row3307_mem, Shared.BasisChunk003.row3308_mem, Shared.BasisChunk003.row3309_mem, Shared.BasisChunk003.row3310_mem, Shared.BasisChunk003.row3311_mem, Shared.BasisChunk003.row3312_mem, Shared.BasisChunk003.row3313_mem, Shared.BasisChunk003.row3314_mem, Shared.BasisChunk003.row3315_mem, Shared.BasisChunk003.row3316_mem, Shared.BasisChunk003.row3317_mem, Shared.BasisChunk003.row3318_mem, Shared.BasisChunk003.row3319_mem, Shared.BasisChunk003.row3320_mem, Shared.BasisChunk003.row3322_mem, Shared.BasisChunk003.row3323_mem, Shared.BasisChunk003.row3326_mem, Shared.BasisChunk003.row3328_mem, Shared.BasisChunk003.row3329_mem, Shared.BasisChunk003.row3330_mem, Shared.BasisChunk003.row3331_mem, Shared.BasisChunk003.row3332_mem, Shared.BasisChunk003.row3333_mem, Shared.BasisChunk003.row3334_mem, Shared.BasisChunk003.row3337_mem, Shared.BasisChunk003.row3341_mem, Shared.BasisChunk003.row3342_mem, Shared.BasisChunk003.row3343_mem, Shared.BasisChunk003.row3344_mem, Shared.BasisChunk003.row3345_mem, Shared.BasisChunk003.row3346_mem, Shared.BasisChunk003.row3347_mem, Shared.BasisChunk003.row3348_mem, Shared.BasisChunk003.row3349_mem, Shared.BasisChunk003.row3350_mem, Shared.BasisChunk003.row3351_mem, Shared.BasisChunk003.row3352_mem, Shared.BasisChunk003.row3353_mem, Shared.BasisChunk003.row3354_mem, Shared.BasisChunk003.row3356_mem, Shared.BasisChunk003.row3357_mem, Shared.BasisChunk003.row3358_mem, Shared.BasisChunk003.row3360_mem, Shared.BasisChunk003.row3361_mem, Shared.BasisChunk003.row3362_mem, Shared.BasisChunk003.row3364_mem, Shared.BasisChunk003.row3365_mem, Shared.BasisChunk003.row3366_mem, Shared.BasisChunk003.row3367_mem, Shared.BasisChunk003.row3368_mem, Shared.BasisChunk003.row3369_mem, Shared.BasisChunk003.row3370_mem, Shared.BasisChunk003.row3371_mem, Shared.BasisChunk003.row3373_mem, Shared.BasisChunk003.row3374_mem, Shared.BasisChunk003.row3375_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard043
