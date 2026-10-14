module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard040
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard040
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard040
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
  exact ⟨Shared.RelationChunk000.relation101_zero, Shared.RelationChunk000.relation105_zero, Shared.RelationChunk000.relation109_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation127_zero, Shared.RelationChunk010.relation539_zero, Shared.RelationChunk010.relation540_zero, Shared.RelationChunk010.relation541_zero, Shared.RelationChunk010.relation549_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation553_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk010.relation555_zero, Shared.RelationChunk010.relation556_zero, Shared.RelationChunk010.relation557_zero, Shared.RelationChunk010.relation558_zero, Shared.RelationChunk010.relation559_zero, Shared.RelationChunk010.relation560_zero, Shared.RelationChunk010.relation561_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5122 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 139, 0, "0,1,434,1"⟩,
  ⟨21, 139, 0, "0,1,8,2,187,1"⟩,
  ⟨20, 139, 2, "0,1,8,2,188,1"⟩,
  ⟨20, 139, 3, "0,1,7,1,278,1"⟩,
  ⟨19, 139, 0, "0,1,22,1,188,1"⟩,
  ⟨19, 139, 1, "0,1,8,1,267,1"⟩,
  ⟨19, 139, 2, "0,2,17,1,209,1"⟩,
  ⟨18, 139, 0, "13,3,75,1"⟩,
  ⟨18, 139, 1, "0,1,23,1,188,1"⟩,
  ⟨18, 139, 2, "0,2,422,1"⟩,
  ⟨17, 139, 0, "13,3,76,1"⟩,
  ⟨17, 139, 1, "0,1,437,1"⟩,
  ⟨16, 139, 1, "0,1,438,1"⟩,
  ⟨16, 139, 2, "0,3,418,1"⟩,
  ⟨15, 139, 1, "3,2,287,1"⟩,
  ⟨15, 139, 2, "0,1,440,1"⟩,
  ⟨15, 139, 3, "0,1,439,1"⟩,
  ⟨14, 139, 0, "449,1"⟩,
  ⟨14, 139, 1, "1,1,7,1,275,1"⟩,
  ⟨14, 139, 2, "0,2,425,1"⟩,
  ⟨13, 139, 1, "0,1,3,1,336,1"⟩,
  ⟨13, 139, 2, "0,11,69,2"⟩,
  ⟨12, 139, 0, "1,1,427,1"⟩,
  ⟨12, 139, 1, "0,2,428,1"⟩,
  ⟨12, 139, 2, "0,11,324,1"⟩,
  ⟨11, 139, 1, "0,1,442,1"⟩,
  ⟨11, 139, 2, "0,1,441,1"⟩,
  ⟨10, 139, 1, "0,1,443,1"⟩,
  ⟨10, 139, 2, "0,2,429,1"⟩,
  ⟨9, 139, 0, "3,1,352,1"⟩,
  ⟨9, 139, 1, "1,1,69,1,95,1"⟩,
  ⟨9, 139, 2, "0,1,445,1"⟩,
  ⟨8, 139, 0, "451,1"⟩,
  ⟨8, 139, 1, "2,2,69,1,76,1"⟩,
  ⟨8, 139, 2, "0,1,3,1,339,1"⟩,
  ⟨8, 139, 3, "0,1,2,1,398,1"⟩,
  ⟨7, 139, 1, "0,1,446,1"⟩,
  ⟨7, 139, 2, "0,1,3,1,340,1"⟩,
  ⟨6, 139, 0, "0,3,3,1,69,2"⟩,
  ⟨5, 139, 1, "0,3,3,1,324,1"⟩,
  ⟨140, 140, 0, "0,140"⟩,
  ⟨46, 140, 0, "0,2,431,1"⟩,
  ⟨45, 140, 1, "0,24,246,1"⟩,
  ⟨42, 140, 0, "0,2,8,2,182,1"⟩,
  ⟨41, 140, 0, "0,2,8,2,183,1"⟩,
  ⟨39, 140, 0, "0,5,402,1"⟩,
  ⟨38, 140, 0, "0,5,403,1"⟩,
  ⟨36, 140, 0, "0,2,432,1"⟩,
  ⟨35, 140, 0, "0,2,433,1"⟩,
  ⟨31, 140, 0, "0,2,8,2,185,1"⟩,
  ⟨28, 140, 0, "8,1,16,1,149,1"⟩,
  ⟨27, 140, 0, "8,1,17,1,149,1"⟩,
  ⟨26, 140, 0, "8,1,277,1"⟩,
  ⟨25, 140, 0, "8,2,193,1"⟩,
  ⟨24, 140, 0, "8,2,194,1"⟩,
  ⟨23, 140, 0, "8,1,13,1,167,1"⟩,
  ⟨22, 140, 0, "13,1,248,1"⟩,
  ⟨21, 140, 0, "454,1"⟩,
  ⟨21, 140, 1, "13,2,150,1"⟩,
  ⟨21, 140, 2, "0,2,8,2,188,1"⟩,
  ⟨20, 140, 1, "0,2,8,1,267,1"⟩,
  ⟨20, 140, 2, "0,3,17,1,209,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row3058_mem, Shared.BasisChunk002.row3059_mem, Shared.BasisChunk002.row3062_mem, Shared.BasisChunk002.row3063_mem, Shared.BasisChunk002.row3064_mem, Shared.BasisChunk002.row3065_mem, Shared.BasisChunk002.row3066_mem, Shared.BasisChunk002.row3067_mem, Shared.BasisChunk002.row3068_mem, Shared.BasisChunk002.row3069_mem, Shared.BasisChunk002.row3070_mem, Shared.BasisChunk002.row3071_mem, Shared.BasisChunk003.row3073_mem, Shared.BasisChunk003.row3074_mem, Shared.BasisChunk003.row3076_mem, Shared.BasisChunk003.row3077_mem, Shared.BasisChunk003.row3078_mem, Shared.BasisChunk003.row3079_mem, Shared.BasisChunk003.row3080_mem, Shared.BasisChunk003.row3081_mem, Shared.BasisChunk003.row3083_mem, Shared.BasisChunk003.row3084_mem, Shared.BasisChunk003.row3085_mem, Shared.BasisChunk003.row3086_mem, Shared.BasisChunk003.row3087_mem, Shared.BasisChunk003.row3089_mem, Shared.BasisChunk003.row3090_mem, Shared.BasisChunk003.row3092_mem, Shared.BasisChunk003.row3093_mem, Shared.BasisChunk003.row3094_mem, Shared.BasisChunk003.row3095_mem, Shared.BasisChunk003.row3096_mem, Shared.BasisChunk003.row3097_mem, Shared.BasisChunk003.row3098_mem, Shared.BasisChunk003.row3099_mem, Shared.BasisChunk003.row3100_mem, Shared.BasisChunk003.row3102_mem, Shared.BasisChunk003.row3103_mem, Shared.BasisChunk003.row3104_mem, Shared.BasisChunk003.row3106_mem, Shared.BasisChunk003.row3108_mem, Shared.BasisChunk003.row3109_mem, Shared.BasisChunk003.row3111_mem, Shared.BasisChunk003.row3112_mem, Shared.BasisChunk003.row3113_mem, Shared.BasisChunk003.row3114_mem, Shared.BasisChunk003.row3115_mem, Shared.BasisChunk003.row3116_mem, Shared.BasisChunk003.row3117_mem, Shared.BasisChunk003.row3119_mem, Shared.BasisChunk003.row3121_mem, Shared.BasisChunk003.row3122_mem, Shared.BasisChunk003.row3123_mem, Shared.BasisChunk003.row3124_mem, Shared.BasisChunk003.row3126_mem, Shared.BasisChunk003.row3127_mem, Shared.BasisChunk003.row3128_mem, Shared.BasisChunk003.row3131_mem, Shared.BasisChunk003.row3132_mem, Shared.BasisChunk003.row3133_mem, Shared.BasisChunk003.row3135_mem, Shared.BasisChunk003.row3136_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard040
