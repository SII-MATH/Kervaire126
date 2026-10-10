import KIP126.LinProgram.Generated.Naturality.Words200.Shard045
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard045
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard045
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
  exact ⟨Shared.RelationChunk000.relation30_zero, Shared.RelationChunk000.relation37_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation131_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation145_zero, Shared.RelationChunk001.relation156_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk002.relation226_zero, Shared.RelationChunk003.relation278_zero, Shared.RelationChunk003.relation279_zero, Shared.RelationChunk003.relation280_zero, Shared.RelationChunk006.relation395_zero, Shared.RelationChunk006.relation396_zero, Shared.RelationChunk006.relation397_zero, Shared.RelationChunk012.relation618_zero, Shared.RelationChunk012.relation619_zero, Shared.RelationChunk012.relation621_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk012.relation626_zero, Shared.RelationChunk012.relation628_zero, Shared.RelationChunk012.relation629_zero, Shared.RelationChunk012.relation630_zero, Shared.RelationChunk012.relation631_zero, Shared.RelationChunk012.relation632_zero, Shared.RelationChunk012.relation633_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5762 128 := by cbv
private def targetRows : List BasisRow := [⟨28, 144, 1, "8,4,13,3"⟩,
  ⟨27, 144, 0, "8,1,17,1,162,1"⟩,
  ⟨27, 144, 1, "8,3,13,2,32,1"⟩,
  ⟨27, 144, 2, "0,1,491,1"⟩,
  ⟨26, 144, 0, "8,2,13,3,23,1"⟩,
  ⟨26, 144, 1, "8,4,89,1"⟩,
  ⟨25, 144, 0, "8,1,13,3,51,1"⟩,
  ⟨25, 144, 1, "8,3,9,1,80,1"⟩,
  ⟨24, 144, 0, "13,6"⟩,
  ⟨24, 144, 2, "8,2,23,1,89,1"⟩,
  ⟨23, 144, 0, "13,3,23,1,24,1"⟩,
  ⟨23, 144, 1, "8,1,299,1"⟩,
  ⟨23, 144, 2, "8,1,9,1,23,1,80,1"⟩,
  ⟨23, 144, 3, "0,1,8,1,291,1"⟩,
  ⟨22, 144, 0, "499,1"⟩,
  ⟨22, 144, 1, "9,1,13,2,101,1"⟩,
  ⟨22, 144, 2, "0,1,8,1,292,1"⟩,
  ⟨20, 144, 0, "8,2,212,1"⟩,
  ⟨20, 144, 1, "0,6,440,1"⟩,
  ⟨19, 144, 0, "13,1,266,1"⟩,
  ⟨19, 144, 1, "8,1,13,1,188,1"⟩,
  ⟨19, 144, 2, "0,5,449,1"⟩,
  ⟨18, 144, 2, "13,1,267,1"⟩,
  ⟨18, 144, 3, "9,1,286,1"⟩,
  ⟨17, 144, 0, "13,1,268,1"⟩,
  ⟨17, 144, 1, "0,2,481,1"⟩,
  ⟨17, 144, 2, "0,2,69,1,112,1"⟩,
  ⟨17, 144, 3, "0,2,2,1,439,1"⟩,
  ⟨17, 144, 4, "0,16,324,1"⟩,
  ⟨16, 144, 0, "0,1,495,1"⟩,
  ⟨16, 144, 1, "0,2,482,1"⟩,
  ⟨16, 144, 2, "0,2,69,1,113,1"⟩,
  ⟨16, 144, 3, "0,3,475,1"⟩,
  ⟨15, 144, 0, "23,1,213,1"⟩,
  ⟨15, 144, 1, "0,1,74,1,107,1"⟩,
  ⟨15, 144, 2, "0,1,3,1,407,1"⟩,
  ⟨14, 144, 0, "9,1,288,1"⟩,
  ⟨14, 144, 3, "0,2,484,1"⟩,
  ⟨13, 144, 1, "0,2,486,1"⟩,
  ⟨13, 144, 2, "0,2,485,1"⟩,
  ⟨13, 144, 3, "0,2,3,1,389,1"⟩,
  ⟨12, 144, 2, "0,1,7,1,311,1"⟩,
  ⟨12, 144, 3, "0,2,3,1,391,1"⟩,
  ⟨12, 144, 4, "0,6,446,1"⟩,
  ⟨11, 144, 2, "0,1,7,1,314,1"⟩,
  ⟨9, 144, 1, "2,1,465,1"⟩,
  ⟨8, 144, 0, "7,1,323,1"⟩,
  ⟨7, 144, 0, "6,1,69,2"⟩,
  ⟨7, 144, 1, "3,1,69,1,93,1"⟩,
  ⟨6, 144, 1, "6,1,324,1"⟩,
  ⟨3, 144, 0, "3,2,324,1"⟩,
  ⟨145, 145, 0, "0,145"⟩,
  ⟨48, 145, 0, "1,1,487,1"⟩,
  ⟨45, 145, 0, "0,1,8,1,295,1"⟩,
  ⟨44, 145, 0, "0,1,8,1,296,1"⟩,
  ⟨37, 145, 0, "0,5,452,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3466_mem, Shared.BasisChunk003.row3467_mem, Shared.BasisChunk003.row3468_mem, Shared.BasisChunk003.row3469_mem, Shared.BasisChunk003.row3470_mem, Shared.BasisChunk003.row3471_mem, Shared.BasisChunk003.row3472_mem, Shared.BasisChunk003.row3473_mem, Shared.BasisChunk003.row3474_mem, Shared.BasisChunk003.row3476_mem, Shared.BasisChunk003.row3477_mem, Shared.BasisChunk003.row3478_mem, Shared.BasisChunk003.row3479_mem, Shared.BasisChunk003.row3480_mem, Shared.BasisChunk003.row3481_mem, Shared.BasisChunk003.row3482_mem, Shared.BasisChunk003.row3483_mem, Shared.BasisChunk003.row3484_mem, Shared.BasisChunk003.row3485_mem, Shared.BasisChunk003.row3486_mem, Shared.BasisChunk003.row3487_mem, Shared.BasisChunk003.row3488_mem, Shared.BasisChunk003.row3491_mem, Shared.BasisChunk003.row3492_mem, Shared.BasisChunk003.row3493_mem, Shared.BasisChunk003.row3494_mem, Shared.BasisChunk003.row3495_mem, Shared.BasisChunk003.row3496_mem, Shared.BasisChunk003.row3497_mem, Shared.BasisChunk003.row3498_mem, Shared.BasisChunk003.row3499_mem, Shared.BasisChunk003.row3500_mem, Shared.BasisChunk003.row3501_mem, Shared.BasisChunk003.row3502_mem, Shared.BasisChunk003.row3503_mem, Shared.BasisChunk003.row3504_mem, Shared.BasisChunk003.row3505_mem, Shared.BasisChunk003.row3508_mem, Shared.BasisChunk003.row3510_mem, Shared.BasisChunk003.row3511_mem, Shared.BasisChunk003.row3512_mem, Shared.BasisChunk003.row3515_mem, Shared.BasisChunk003.row3516_mem, Shared.BasisChunk003.row3517_mem, Shared.BasisChunk003.row3520_mem, Shared.BasisChunk003.row3523_mem, Shared.BasisChunk003.row3524_mem, Shared.BasisChunk003.row3526_mem, Shared.BasisChunk003.row3527_mem, Shared.BasisChunk003.row3530_mem, Shared.BasisChunk003.row3534_mem, Shared.BasisChunk003.row3536_mem, Shared.BasisChunk003.row3537_mem, Shared.BasisChunk003.row3538_mem, Shared.BasisChunk003.row3539_mem, Shared.BasisChunk003.row3540_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard045
