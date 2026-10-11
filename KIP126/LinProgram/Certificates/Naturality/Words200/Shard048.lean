module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard048
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard048
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard048
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation145_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation218_zero, Shared.RelationChunk002.relation220_zero, Shared.RelationChunk002.relation221_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk004.relation293_zero, Shared.RelationChunk004.relation296_zero, Shared.RelationChunk004.relation297_zero, Shared.RelationChunk004.relation298_zero, Shared.RelationChunk004.relation299_zero, Shared.RelationChunk005.relation328_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk006.relation406_zero, Shared.RelationChunk007.relation423_zero, Shared.RelationChunk007.relation425_zero, Shared.RelationChunk007.relation427_zero, Shared.RelationChunk007.relation428_zero, Shared.RelationChunk007.relation429_zero, Shared.RelationChunk007.relation430_zero, Shared.RelationChunk008.relation443_zero, Shared.RelationChunk013.relation678_zero, Shared.RelationChunk013.relation679_zero, Shared.RelationChunk013.relation680_zero, Shared.RelationChunk013.relation681_zero, Shared.RelationChunk013.relation682_zero, Shared.RelationChunk013.relation683_zero, Shared.RelationChunk013.relation684_zero, Shared.RelationChunk013.relation685_zero, Shared.RelationChunk013.relation686_zero, Shared.RelationChunk013.relation687_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6146 128 := by cbv
private def targetRows : List BasisRow := [⟨147, 147, 0, "0,147"⟩,
  ⟨43, 147, 0, "8,1,326,1"⟩,
  ⟨42, 147, 0, "17,1,253,1"⟩,
  ⟨41, 147, 0, "528,1"⟩,
  ⟨40, 147, 0, "8,3,152,1"⟩,
  ⟨39, 147, 0, "8,3,153,1"⟩,
  ⟨38, 147, 0, "8,2,17,1,117,1"⟩,
  ⟨37, 147, 0, "8,2,223,1"⟩,
  ⟨36, 147, 0, "8,5,55,1"⟩,
  ⟨35, 147, 0, "8,5,56,1"⟩,
  ⟨34, 147, 1, "8,4,17,1,40,1"⟩,
  ⟨33, 147, 0, "8,2,225,1"⟩,
  ⟨33, 147, 1, "8,4,100,1"⟩,
  ⟨33, 147, 2, "0,1,16,1,244,1"⟩,
  ⟨32, 147, 0, "16,1,17,1,138,1"⟩,
  ⟨32, 147, 1, "8,7,9,1"⟩,
  ⟨32, 147, 2, "0,1,17,1,244,1"⟩,
  ⟨31, 147, 1, "17,2,138,1"⟩,
  ⟨31, 147, 2, "8,6,29,1"⟩,
  ⟨30, 147, 0, "8,3,16,1,64,1"⟩,
  ⟨30, 147, 1, "8,5,9,1,23,1"⟩,
  ⟨30, 147, 2, "0,4,491,1"⟩,
  ⟨29, 147, 0, "8,3,17,1,64,1"⟩,
  ⟨29, 147, 1, "8,4,9,1,51,1"⟩,
  ⟨29, 147, 2, "0,2,509,1"⟩,
  ⟨28, 147, 0, "8,3,154,1"⟩,
  ⟨28, 147, 1, "8,3,9,1,13,3"⟩,
  ⟨27, 147, 0, "8,2,42,1,64,1"⟩,
  ⟨27, 147, 1, "8,2,9,1,13,2,32,1"⟩,
  ⟨27, 147, 2, "0,1,516,1"⟩,
  ⟨26, 147, 0, "529,1"⟩,
  ⟨26, 147, 1, "8,1,9,1,13,3,23,1"⟩,
  ⟨26, 147, 2, "8,4,101,1"⟩,
  ⟨25, 147, 0, "9,1,13,3,51,1"⟩,
  ⟨25, 147, 1, "8,3,13,1,80,1"⟩,
  ⟨24, 147, 0, "8,1,64,1,72,1"⟩,
  ⟨24, 147, 1, "8,2,23,1,101,1"⟩,
  ⟨24, 147, 2, "1,1,5,1,347,1"⟩,
  ⟨23, 147, 0, "8,1,327,1"⟩,
  ⟨23, 147, 1, "8,1,13,1,23,1,80,1"⟩,
  ⟨23, 147, 2, "0,1,8,1,316,1"⟩,
  ⟨23, 147, 3, "0,9,440,1"⟩,
  ⟨22, 147, 0, "17,1,255,1"⟩,
  ⟨22, 147, 1, "13,3,101,1"⟩,
  ⟨22, 147, 2, "0,1,9,1,292,1"⟩,
  ⟨22, 147, 3, "0,8,449,1"⟩,
  ⟨21, 147, 0, "530,1"⟩,
  ⟨21, 147, 1, "1,1,510,1"⟩,
  ⟨21, 147, 2, "0,3,500,1"⟩,
  ⟨20, 147, 0, "8,1,9,1,212,1"⟩,
  ⟨20, 147, 1, "0,5,481,1"⟩,
  ⟨20, 147, 2, "0,19,324,1"⟩,
  ⟨19, 147, 0, "9,1,13,1,188,1"⟩,
  ⟨19, 147, 1, "0,5,482,1"⟩,
  ⟨18, 147, 0, "13,1,286,1"⟩,
  ⟨18, 147, 1, "0,1,3,1,437,1"⟩,
  ⟨17, 147, 1, "0,2,8,1,64,1,69,1"⟩,
  ⟨17, 147, 2, "0,5,484,1"⟩,
  ⟨16, 147, 0, "0,2,8,1,312,1"⟩,
  ⟨15, 147, 0, "0,2,3,1,425,1"⟩,
  ⟨15, 147, 1, "0,4,7,1,311,1"⟩,
  ⟨14, 147, 1, "13,1,288,1"⟩,
  ⟨14, 147, 2, "0,1,2,1,484,1"⟩,
  ⟨14, 147, 3, "0,4,7,1,314,1"⟩,
  ⟨13, 147, 1, "532,1"⟩,
  ⟨13, 147, 4, "0,1,2,1,486,1"⟩,
  ⟨12, 147, 0, "534,1"⟩,
  ⟨12, 147, 1, "43,1,174,1"⟩,
  ⟨12, 147, 2, "7,1,351,1"⟩,
  ⟨12, 147, 3, "0,2,7,1,333,1"⟩,
  ⟨11, 147, 0, "0,1,521,1"⟩,
  ⟨11, 147, 1, "0,2,513,1"⟩,
  ⟨10, 147, 0, "3,2,352,1"⟩,
  ⟨10, 147, 2, "0,1,523,1"⟩,
  ⟨9, 147, 1, "7,1,352,1"⟩,
  ⟨9, 147, 2, "0,1,524,1"⟩,
  ⟨9, 147, 3, "0,3,505,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3698_mem, Shared.BasisChunk003.row3700_mem, Shared.BasisChunk003.row3701_mem, Shared.BasisChunk003.row3702_mem, Shared.BasisChunk003.row3703_mem, Shared.BasisChunk003.row3704_mem, Shared.BasisChunk003.row3705_mem, Shared.BasisChunk003.row3706_mem, Shared.BasisChunk003.row3707_mem, Shared.BasisChunk003.row3708_mem, Shared.BasisChunk003.row3710_mem, Shared.BasisChunk003.row3711_mem, Shared.BasisChunk003.row3712_mem, Shared.BasisChunk003.row3713_mem, Shared.BasisChunk003.row3714_mem, Shared.BasisChunk003.row3715_mem, Shared.BasisChunk003.row3716_mem, Shared.BasisChunk003.row3718_mem, Shared.BasisChunk003.row3719_mem, Shared.BasisChunk003.row3720_mem, Shared.BasisChunk003.row3721_mem, Shared.BasisChunk003.row3722_mem, Shared.BasisChunk003.row3723_mem, Shared.BasisChunk003.row3724_mem, Shared.BasisChunk003.row3725_mem, Shared.BasisChunk003.row3726_mem, Shared.BasisChunk003.row3727_mem, Shared.BasisChunk003.row3729_mem, Shared.BasisChunk003.row3730_mem, Shared.BasisChunk003.row3731_mem, Shared.BasisChunk003.row3732_mem, Shared.BasisChunk003.row3733_mem, Shared.BasisChunk003.row3734_mem, Shared.BasisChunk003.row3735_mem, Shared.BasisChunk003.row3736_mem, Shared.BasisChunk003.row3737_mem, Shared.BasisChunk003.row3738_mem, Shared.BasisChunk003.row3739_mem, Shared.BasisChunk003.row3740_mem, Shared.BasisChunk003.row3741_mem, Shared.BasisChunk003.row3742_mem, Shared.BasisChunk003.row3743_mem, Shared.BasisChunk003.row3744_mem, Shared.BasisChunk003.row3745_mem, Shared.BasisChunk003.row3746_mem, Shared.BasisChunk003.row3747_mem, Shared.BasisChunk003.row3748_mem, Shared.BasisChunk003.row3749_mem, Shared.BasisChunk003.row3750_mem, Shared.BasisChunk003.row3751_mem, Shared.BasisChunk003.row3752_mem, Shared.BasisChunk003.row3753_mem, Shared.BasisChunk003.row3754_mem, Shared.BasisChunk003.row3755_mem, Shared.BasisChunk003.row3756_mem, Shared.BasisChunk003.row3757_mem, Shared.BasisChunk003.row3759_mem, Shared.BasisChunk003.row3760_mem, Shared.BasisChunk003.row3761_mem, Shared.BasisChunk003.row3762_mem, Shared.BasisChunk003.row3763_mem, Shared.BasisChunk003.row3765_mem, Shared.BasisChunk003.row3766_mem, Shared.BasisChunk003.row3767_mem, Shared.BasisChunk003.row3769_mem, Shared.BasisChunk003.row3772_mem, Shared.BasisChunk003.row3773_mem, Shared.BasisChunk003.row3774_mem, Shared.BasisChunk003.row3775_mem, Shared.BasisChunk003.row3776_mem, Shared.BasisChunk003.row3777_mem, Shared.BasisChunk003.row3778_mem, Shared.BasisChunk003.row3779_mem, Shared.BasisChunk003.row3781_mem, Shared.BasisChunk003.row3783_mem, Shared.BasisChunk003.row3784_mem, Shared.BasisChunk003.row3785_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard048
