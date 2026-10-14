module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard046
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard046
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard046
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
  exact ⟨Shared.RelationChunk000.relation5_zero, Shared.RelationChunk005.relation360_zero, Shared.RelationChunk005.relation361_zero, Shared.RelationChunk010.relation569_zero, Shared.RelationChunk012.relation639_zero, Shared.RelationChunk012.relation640_zero, Shared.RelationChunk012.relation641_zero, Shared.RelationChunk012.relation642_zero, Shared.RelationChunk012.relation643_zero, Shared.RelationChunk012.relation644_zero, Shared.RelationChunk012.relation646_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5890 128 := by cbv
private def targetRows : List BasisRow := [⟨36, 145, 0, "0,4,17,1,225,1"⟩,
  ⟨35, 145, 0, "0,1,8,1,297,1"⟩,
  ⟨34, 145, 0, "0,1,8,1,298,1"⟩,
  ⟨34, 145, 1, "0,2,488,1"⟩,
  ⟨33, 145, 0, "0,1,17,1,238,1"⟩,
  ⟨28, 145, 0, "0,2,491,1"⟩,
  ⟨27, 145, 0, "509,1"⟩,
  ⟨25, 145, 0, "0,1,8,1,64,2"⟩,
  ⟨24, 145, 0, "0,1,8,1,299,1"⟩,
  ⟨24, 145, 1, "0,2,8,1,291,1"⟩,
  ⟨23, 145, 1, "0,2,8,1,292,1"⟩,
  ⟨21, 145, 0, "0,1,8,2,212,1"⟩,
  ⟨21, 145, 1, "0,7,440,1"⟩,
  ⟨20, 145, 1, "0,1,8,1,13,1,188,1"⟩,
  ⟨20, 145, 2, "0,6,449,1"⟩,
  ⟨19, 145, 0, "13,3,95,1"⟩,
  ⟨19, 145, 1, "0,1,500,1"⟩,
  ⟨18, 145, 0, "13,2,164,1"⟩,
  ⟨18, 145, 1, "1,1,493,1"⟩,
  ⟨18, 145, 2, "0,3,481,1"⟩,
  ⟨18, 145, 3, "0,3,69,1,112,1"⟩,
  ⟨18, 145, 4, "0,17,324,1"⟩,
  ⟨17, 145, 0, "2,1,473,1"⟩,
  ⟨17, 145, 2, "0,3,482,1"⟩,
  ⟨16, 145, 0, "7,1,328,1"⟩,
  ⟨15, 145, 1, "0,1,7,1,319,1"⟩,
  ⟨15, 145, 2, "0,3,484,1"⟩,
  ⟨14, 145, 0, "8,1,312,1"⟩,
  ⟨14, 145, 1, "1,1,76,1,107,1"⟩,
  ⟨14, 145, 2, "0,1,502,1"⟩,
  ⟨13, 145, 0, "8,1,314,1"⟩,
  ⟨13, 145, 2, "1,1,497,1"⟩,
  ⟨13, 145, 3, "0,2,7,1,311,1"⟩,
  ⟨12, 145, 1, "1,1,3,1,412,1"⟩,
  ⟨12, 145, 2, "0,2,7,1,314,1"⟩,
  ⟨11, 145, 0, "3,1,428,1"⟩,
  ⟨11, 145, 1, "3,2,333,1"⟩,
  ⟨11, 145, 2, "0,1,7,1,322,1"⟩,
  ⟨10, 145, 0, "512,1"⟩,
  ⟨10, 145, 2, "2,1,479,1"⟩,
  ⟨10, 145, 3, "0,1,504,1"⟩,
  ⟨9, 145, 0, "514,1"⟩,
  ⟨8, 145, 0, "0,1,6,1,69,2"⟩,
  ⟨7, 145, 0, "0,1,505,1"⟩,
  ⟨7, 145, 1, "0,1,6,1,324,1"⟩,
  ⟨6, 145, 0, "0,1,507,1"⟩,
  ⟨6, 145, 1, "0,1,506,1"⟩,
  ⟨5, 145, 0, "0,1,508,1"⟩,
  ⟨4, 145, 0, "0,1,3,2,324,1"⟩,
  ⟨3, 145, 0, "0,1,7,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3541_mem, Shared.BasisChunk003.row3542_mem, Shared.BasisChunk003.row3543_mem, Shared.BasisChunk003.row3544_mem, Shared.BasisChunk003.row3545_mem, Shared.BasisChunk003.row3546_mem, Shared.BasisChunk003.row3547_mem, Shared.BasisChunk003.row3549_mem, Shared.BasisChunk003.row3550_mem, Shared.BasisChunk003.row3551_mem, Shared.BasisChunk003.row3553_mem, Shared.BasisChunk003.row3554_mem, Shared.BasisChunk003.row3555_mem, Shared.BasisChunk003.row3557_mem, Shared.BasisChunk003.row3558_mem, Shared.BasisChunk003.row3559_mem, Shared.BasisChunk003.row3560_mem, Shared.BasisChunk003.row3561_mem, Shared.BasisChunk003.row3562_mem, Shared.BasisChunk003.row3563_mem, Shared.BasisChunk003.row3564_mem, Shared.BasisChunk003.row3565_mem, Shared.BasisChunk003.row3566_mem, Shared.BasisChunk003.row3568_mem, Shared.BasisChunk003.row3569_mem, Shared.BasisChunk003.row3572_mem, Shared.BasisChunk003.row3573_mem, Shared.BasisChunk003.row3574_mem, Shared.BasisChunk003.row3575_mem, Shared.BasisChunk003.row3576_mem, Shared.BasisChunk003.row3577_mem, Shared.BasisChunk003.row3579_mem, Shared.BasisChunk003.row3580_mem, Shared.BasisChunk003.row3582_mem, Shared.BasisChunk003.row3583_mem, Shared.BasisChunk003.row3584_mem, Shared.BasisChunk003.row3585_mem, Shared.BasisChunk003.row3586_mem, Shared.BasisChunk003.row3587_mem, Shared.BasisChunk003.row3589_mem, Shared.BasisChunk003.row3590_mem, Shared.BasisChunk003.row3591_mem, Shared.BasisChunk003.row3593_mem, Shared.BasisChunk003.row3594_mem, Shared.BasisChunk003.row3595_mem, Shared.BasisChunk003.row3596_mem, Shared.BasisChunk003.row3597_mem, Shared.BasisChunk003.row3598_mem, Shared.BasisChunk003.row3599_mem, Shared.BasisChunk003.row3600_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard046
