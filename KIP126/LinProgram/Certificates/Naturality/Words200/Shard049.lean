import KIP126.LinProgram.Generated.Naturality.Words200.Shard049
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard049
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard049
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk001.relation162_zero, Shared.RelationChunk001.relation163_zero, Shared.RelationChunk002.relation244_zero, Shared.RelationChunk012.relation649_zero, Shared.RelationChunk012.relation650_zero, Shared.RelationChunk012.relation651_zero, Shared.RelationChunk013.relation676_zero, Shared.RelationChunk013.relation698_zero, Shared.RelationChunk013.relation699_zero, Shared.RelationChunk013.relation700_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6274 128 := by cbv
private def targetRows : List BasisRow := [⟨8, 147, 0, "7,1,353,1"⟩,
  ⟨8, 147, 1, "0,3,507,1"⟩,
  ⟨8, 147, 2, "0,3,506,1"⟩,
  ⟨7, 147, 0, "0,1,8,1,69,2"⟩,
  ⟨7, 147, 1, "0,3,508,1"⟩,
  ⟨6, 147, 0, "0,1,526,1"⟩,
  ⟨6, 147, 1, "0,1,8,1,324,1"⟩,
  ⟨5, 147, 0, "0,3,7,1,324,1"⟩,
  ⟨148, 148, 0, "0,148"⟩,
  ⟨49, 148, 0, "536,1"⟩,
  ⟨45, 148, 0, "0,1,8,1,325,1"⟩,
  ⟨44, 148, 0, "0,1,8,1,326,1"⟩,
  ⟨43, 148, 0, "0,1,17,1,253,1"⟩,
  ⟨35, 148, 0, "0,1,8,2,224,1"⟩,
  ⟨34, 148, 0, "0,1,8,2,225,1"⟩,
  ⟨34, 148, 1, "0,2,16,1,244,1"⟩,
  ⟨33, 148, 0, "0,1,16,1,17,1,138,1"⟩,
  ⟨33, 148, 1, "0,2,17,1,244,1"⟩,
  ⟨32, 148, 0, "0,1,17,2,138,1"⟩,
  ⟨31, 148, 0, "0,5,491,1"⟩,
  ⟨30, 148, 0, "0,3,509,1"⟩,
  ⟨28, 148, 0, "0,2,516,1"⟩,
  ⟨27, 148, 0, "0,1,529,1"⟩,
  ⟨24, 148, 0, "0,2,8,1,316,1"⟩,
  ⟨24, 148, 1, "0,10,440,1"⟩,
  ⟨23, 148, 0, "0,2,9,1,292,1"⟩,
  ⟨23, 148, 1, "0,9,449,1"⟩,
  ⟨22, 148, 0, "0,1,530,1"⟩,
  ⟨22, 148, 1, "0,4,500,1"⟩,
  ⟨21, 148, 0, "537,1"⟩,
  ⟨21, 148, 1, "13,3,105,1"⟩,
  ⟨21, 148, 2, "0,6,481,1"⟩,
  ⟨21, 148, 3, "0,20,324,1"⟩,
  ⟨20, 148, 1, "9,1,13,1,23,1,75,1"⟩,
  ⟨20, 148, 2, "0,6,482,1"⟩,
  ⟨19, 148, 1, "0,1,13,1,286,1"⟩,
  ⟨18, 148, 0, "539,1"⟩,
  ⟨16, 148, 0, "0,5,7,1,311,1"⟩,
  ⟨15, 148, 1, "0,5,7,1,314,1"⟩,
  ⟨14, 148, 0, "8,1,337,1"⟩,
  ⟨14, 148, 1, "3,2,363,1"⟩,
  ⟨14, 148, 2, "0,1,533,1"⟩,
  ⟨14, 148, 3, "0,1,8,1,333,1"⟩,
  ⟨14, 148, 4, "0,2,2,1,486,1"⟩,
  ⟨13, 148, 1, "8,1,338,1"⟩,
  ⟨13, 148, 2, "0,1,534,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3786_mem, Shared.BasisChunk003.row3787_mem, Shared.BasisChunk003.row3788_mem, Shared.BasisChunk003.row3789_mem, Shared.BasisChunk003.row3790_mem, Shared.BasisChunk003.row3791_mem, Shared.BasisChunk003.row3792_mem, Shared.BasisChunk003.row3793_mem, Shared.BasisChunk003.row3794_mem, Shared.BasisChunk003.row3796_mem, Shared.BasisChunk003.row3797_mem, Shared.BasisChunk003.row3798_mem, Shared.BasisChunk003.row3799_mem, Shared.BasisChunk003.row3800_mem, Shared.BasisChunk003.row3801_mem, Shared.BasisChunk003.row3802_mem, Shared.BasisChunk003.row3803_mem, Shared.BasisChunk003.row3804_mem, Shared.BasisChunk003.row3805_mem, Shared.BasisChunk003.row3806_mem, Shared.BasisChunk003.row3807_mem, Shared.BasisChunk003.row3808_mem, Shared.BasisChunk003.row3809_mem, Shared.BasisChunk003.row3810_mem, Shared.BasisChunk003.row3811_mem, Shared.BasisChunk003.row3812_mem, Shared.BasisChunk003.row3813_mem, Shared.BasisChunk003.row3814_mem, Shared.BasisChunk003.row3815_mem, Shared.BasisChunk003.row3816_mem, Shared.BasisChunk003.row3817_mem, Shared.BasisChunk003.row3818_mem, Shared.BasisChunk003.row3819_mem, Shared.BasisChunk003.row3821_mem, Shared.BasisChunk003.row3822_mem, Shared.BasisChunk003.row3824_mem, Shared.BasisChunk003.row3825_mem, Shared.BasisChunk003.row3826_mem, Shared.BasisChunk003.row3828_mem, Shared.BasisChunk003.row3829_mem, Shared.BasisChunk003.row3830_mem, Shared.BasisChunk003.row3831_mem, Shared.BasisChunk003.row3832_mem, Shared.BasisChunk003.row3833_mem, Shared.BasisChunk003.row3835_mem, Shared.BasisChunk003.row3836_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard049
