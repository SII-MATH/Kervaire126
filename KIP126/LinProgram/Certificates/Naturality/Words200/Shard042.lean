import KIP126.LinProgram.Generated.Naturality.Words200.Shard042
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard042
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard042
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
  exact ⟨Shared.RelationChunk000.relation35_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk001.relation145_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation367_zero, Shared.RelationChunk006.relation368_zero, Shared.RelationChunk006.relation369_zero, Shared.RelationChunk010.relation522_zero, Shared.RelationChunk010.relation523_zero, Shared.RelationChunk010.relation524_zero, Shared.RelationChunk010.relation567_zero, Shared.RelationChunk010.relation571_zero, Shared.RelationChunk011.relation573_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation575_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk011.relation577_zero, Shared.RelationChunk011.relation578_zero, Shared.RelationChunk011.relation579_zero, Shared.RelationChunk011.relation580_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5378 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 141, 1, "8,2,23,1,80,1"⟩,
  ⟨23, 141, 2, "0,1,8,1,278,1"⟩,
  ⟨22, 141, 0, "471,1"⟩,
  ⟨22, 141, 1, "8,1,13,2,101,1"⟩,
  ⟨22, 141, 2, "0,1,454,1"⟩,
  ⟨21, 141, 0, "13,3,80,1"⟩,
  ⟨21, 141, 2, "0,1,455,1"⟩,
  ⟨21, 141, 3, "0,4,17,1,209,1"⟩,
  ⟨20, 141, 1, "0,4,422,1"⟩,
  ⟨19, 141, 0, "8,1,9,1,188,1"⟩,
  ⟨19, 141, 1, "0,3,437,1"⟩,
  ⟨18, 141, 0, "9,1,267,1"⟩,
  ⟨18, 141, 1, "0,1,3,1,359,1"⟩,
  ⟨18, 141, 2, "0,5,418,1"⟩,
  ⟨17, 141, 0, "472,1"⟩,
  ⟨17, 141, 1, "0,2,448,1"⟩,
  ⟨17, 141, 2, "0,3,440,1"⟩,
  ⟨17, 141, 3, "0,3,439,1"⟩,
  ⟨16, 141, 0, "473,1"⟩,
  ⟨16, 141, 2, "0,1,67,1,107,1"⟩,
  ⟨16, 141, 3, "0,2,449,1"⟩,
  ⟨15, 141, 0, "0,1,68,1,107,1"⟩,
  ⟨15, 141, 1, "0,13,69,2"⟩,
  ⟨14, 141, 0, "0,1,13,1,251,1"⟩,
  ⟨14, 141, 1, "0,1,3,1,363,1"⟩,
  ⟨14, 141, 2, "0,13,324,1"⟩,
  ⟨13, 141, 1, "474,1"⟩,
  ⟨13, 141, 2, "0,1,460,1"⟩,
  ⟨13, 141, 3, "0,1,3,1,365,1"⟩,
  ⟨12, 141, 0, "476,1"⟩,
  ⟨12, 141, 1, "0,1,462,1"⟩,
  ⟨12, 141, 2, "0,2,450,1"⟩,
  ⟨11, 141, 1, "1,1,450,1"⟩,
  ⟨10, 141, 1, "2,2,376,1"⟩,
  ⟨10, 141, 2, "0,1,464,1"⟩,
  ⟨10, 141, 3, "0,2,451,1"⟩,
  ⟨9, 141, 2, "2,1,69,1,95,1"⟩,
  ⟨9, 141, 3, "0,1,465,1"⟩,
  ⟨9, 141, 4, "0,3,446,1"⟩,
  ⟨8, 141, 1, "1,1,3,1,69,1,76,1"⟩,
  ⟨7, 141, 0, "3,1,377,1"⟩,
  ⟨6, 141, 0, "3,1,378,1"⟩,
  ⟨6, 141, 1, "1,1,4,1,69,2"⟩,
  ⟨5, 141, 0, "1,1,4,1,324,1"⟩,
  ⟨142, 142, 0, "0,142"⟩,
  ⟨47, 142, 0, "0,26,246,1"⟩,
  ⟨45, 142, 0, "0,1,469,1"⟩,
  ⟨44, 142, 0, "0,1,470,1"⟩,
  ⟨41, 142, 0, "0,7,402,1"⟩,
  ⟨40, 142, 0, "0,7,403,1"⟩,
  ⟨35, 142, 0, "0,1,16,1,224,1"⟩,
  ⟨34, 142, 0, "0,1,16,1,225,1"⟩,
  ⟨34, 142, 1, "0,2,452,1"⟩,
  ⟨33, 142, 1, "0,1,17,1,225,1"⟩,
  ⟨31, 142, 0, "0,1,8,3,137,1"⟩,
  ⟨30, 142, 1, "0,1,8,3,138,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3233_mem, Shared.BasisChunk003.row3234_mem, Shared.BasisChunk003.row3235_mem, Shared.BasisChunk003.row3236_mem, Shared.BasisChunk003.row3237_mem, Shared.BasisChunk003.row3238_mem, Shared.BasisChunk003.row3240_mem, Shared.BasisChunk003.row3241_mem, Shared.BasisChunk003.row3243_mem, Shared.BasisChunk003.row3244_mem, Shared.BasisChunk003.row3245_mem, Shared.BasisChunk003.row3246_mem, Shared.BasisChunk003.row3247_mem, Shared.BasisChunk003.row3248_mem, Shared.BasisChunk003.row3249_mem, Shared.BasisChunk003.row3250_mem, Shared.BasisChunk003.row3251_mem, Shared.BasisChunk003.row3252_mem, Shared.BasisChunk003.row3253_mem, Shared.BasisChunk003.row3255_mem, Shared.BasisChunk003.row3256_mem, Shared.BasisChunk003.row3257_mem, Shared.BasisChunk003.row3258_mem, Shared.BasisChunk003.row3259_mem, Shared.BasisChunk003.row3260_mem, Shared.BasisChunk003.row3261_mem, Shared.BasisChunk003.row3263_mem, Shared.BasisChunk003.row3264_mem, Shared.BasisChunk003.row3265_mem, Shared.BasisChunk003.row3266_mem, Shared.BasisChunk003.row3267_mem, Shared.BasisChunk003.row3268_mem, Shared.BasisChunk003.row3270_mem, Shared.BasisChunk003.row3272_mem, Shared.BasisChunk003.row3273_mem, Shared.BasisChunk003.row3274_mem, Shared.BasisChunk003.row3277_mem, Shared.BasisChunk003.row3278_mem, Shared.BasisChunk003.row3279_mem, Shared.BasisChunk003.row3281_mem, Shared.BasisChunk003.row3282_mem, Shared.BasisChunk003.row3283_mem, Shared.BasisChunk003.row3284_mem, Shared.BasisChunk003.row3285_mem, Shared.BasisChunk003.row3286_mem, Shared.BasisChunk003.row3287_mem, Shared.BasisChunk003.row3289_mem, Shared.BasisChunk003.row3290_mem, Shared.BasisChunk003.row3291_mem, Shared.BasisChunk003.row3292_mem, Shared.BasisChunk003.row3293_mem, Shared.BasisChunk003.row3294_mem, Shared.BasisChunk003.row3295_mem, Shared.BasisChunk003.row3297_mem, Shared.BasisChunk003.row3298_mem, Shared.BasisChunk003.row3300_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard042
