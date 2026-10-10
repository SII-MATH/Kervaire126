import KIP126.LinProgram.Generated.Naturality.Words200.Shard047
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard047
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard047
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
  exact ⟨Shared.RelationChunk000.relation12_zero, Shared.RelationChunk000.relation21_zero, Shared.RelationChunk000.relation44_zero, Shared.RelationChunk001.relation160_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk007.relation417_zero, Shared.RelationChunk007.relation436_zero, Shared.RelationChunk007.relation437_zero, Shared.RelationChunk012.relation647_zero, Shared.RelationChunk012.relation648_zero, Shared.RelationChunk012.relation651_zero, Shared.RelationChunk012.relation653_zero, Shared.RelationChunk012.relation654_zero, Shared.RelationChunk012.relation655_zero, Shared.RelationChunk012.relation656_zero, Shared.RelationChunk012.relation657_zero, Shared.RelationChunk012.relation658_zero, Shared.RelationChunk012.relation659_zero, Shared.RelationChunk012.relation660_zero, Shared.RelationChunk012.relation661_zero, Shared.RelationChunk012.relation662_zero, Shared.RelationChunk012.relation663_zero, Shared.RelationChunk013.relation664_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk013.relation670_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk013.relation672_zero, Shared.RelationChunk013.relation673_zero, Shared.RelationChunk013.relation674_zero, Shared.RelationChunk013.relation675_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6018 128 := by cbv
private def targetRows : List BasisRow := [⟨146, 146, 0, "0,146"⟩,
  ⟨46, 146, 0, "0,2,8,1,295,1"⟩,
  ⟨45, 146, 0, "0,2,8,1,296,1"⟩,
  ⟨38, 146, 0, "0,6,452,1"⟩,
  ⟨37, 146, 0, "0,5,17,1,225,1"⟩,
  ⟨36, 146, 0, "0,2,8,1,297,1"⟩,
  ⟨35, 146, 0, "0,2,8,1,298,1"⟩,
  ⟨35, 146, 1, "0,3,488,1"⟩,
  ⟨31, 146, 0, "17,1,244,1"⟩,
  ⟨30, 146, 0, "16,1,245,1"⟩,
  ⟨29, 146, 0, "8,1,315,1"⟩,
  ⟨29, 146, 1, "0,3,491,1"⟩,
  ⟨28, 146, 0, "8,3,149,1"⟩,
  ⟨28, 146, 1, "0,1,509,1"⟩,
  ⟨27, 146, 0, "8,1,16,1,167,1"⟩,
  ⟨26, 146, 1, "8,2,218,1"⟩,
  ⟨25, 146, 0, "8,2,219,1"⟩,
  ⟨25, 146, 1, "0,2,8,1,299,1"⟩,
  ⟨24, 146, 0, "8,1,13,1,194,1"⟩,
  ⟨23, 146, 0, "13,2,167,1"⟩,
  ⟨22, 146, 1, "13,2,168,1"⟩,
  ⟨22, 146, 3, "0,8,440,1"⟩,
  ⟨21, 146, 1, "9,1,292,1"⟩,
  ⟨21, 146, 2, "0,7,449,1"⟩,
  ⟨20, 146, 1, "0,2,500,1"⟩,
  ⟨19, 146, 0, "9,1,293,1"⟩,
  ⟨19, 146, 2, "1,1,500,1"⟩,
  ⟨19, 146, 3, "0,4,481,1"⟩,
  ⟨19, 146, 4, "0,18,324,1"⟩,
  ⟨18, 146, 1, "8,1,9,1,209,1"⟩,
  ⟨18, 146, 2, "0,4,482,1"⟩,
  ⟨17, 146, 0, "9,1,294,1"⟩,
  ⟨17, 146, 1, "3,1,437,1"⟩,
  ⟨16, 146, 0, "3,1,438,1"⟩,
  ⟨16, 146, 1, "0,1,8,1,64,1,69,1"⟩,
  ⟨16, 146, 2, "0,2,7,1,319,1"⟩,
  ⟨16, 146, 3, "0,4,484,1"⟩,
  ⟨15, 146, 0, "2,1,482,1"⟩,
  ⟨15, 146, 2, "1,1,3,1,417,1"⟩,
  ⟨15, 146, 3, "0,1,8,1,312,1"⟩,
  ⟨15, 146, 4, "0,2,502,1"⟩,
  ⟨14, 146, 0, "13,1,281,1"⟩,
  ⟨14, 146, 1, "3,2,335,1"⟩,
  ⟨14, 146, 2, "0,1,8,1,314,1"⟩,
  ⟨14, 146, 3, "0,1,3,1,425,1"⟩,
  ⟨14, 146, 4, "0,3,7,1,311,1"⟩,
  ⟨13, 146, 0, "7,1,335,1"⟩,
  ⟨13, 146, 1, "2,1,484,1"⟩,
  ⟨13, 146, 2, "1,2,486,1"⟩,
  ⟨13, 146, 3, "1,2,485,1"⟩,
  ⟨13, 146, 4, "0,3,7,1,314,1"⟩,
  ⟨12, 146, 0, "2,1,486,1"⟩,
  ⟨12, 146, 3, "0,1,3,1,428,1"⟩,
  ⟨12, 146, 4, "0,1,3,2,333,1"⟩,
  ⟨11, 146, 0, "520,1"⟩,
  ⟨11, 146, 1, "1,1,7,1,322,1"⟩,
  ⟨11, 146, 2, "0,1,512,1"⟩,
  ⟨11, 146, 3, "0,1,7,1,333,1"⟩,
  ⟨11, 146, 4, "0,1,2,1,479,1"⟩,
  ⟨11, 146, 5, "0,2,504,1"⟩,
  ⟨10, 146, 0, "522,1"⟩,
  ⟨10, 146, 2, "1,1,504,1"⟩,
  ⟨10, 146, 3, "0,1,514,1"⟩,
  ⟨10, 146, 4, "0,1,513,1"⟩,
  ⟨9, 146, 1, "0,2,6,1,69,2"⟩,
  ⟨8, 146, 1, "0,2,505,1"⟩,
  ⟨8, 146, 2, "0,2,6,1,324,1"⟩,
  ⟨7, 146, 1, "1,1,505,1"⟩,
  ⟨7, 146, 2, "0,2,507,1"⟩,
  ⟨7, 146, 3, "0,2,506,1"⟩,
  ⟨6, 146, 1, "1,1,507,1"⟩,
  ⟨6, 146, 3, "0,2,508,1"⟩,
  ⟨5, 146, 0, "526,1"⟩,
  ⟨5, 146, 2, "1,1,508,1"⟩,
  ⟨4, 146, 1, "0,2,7,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3601_mem, Shared.BasisChunk003.row3603_mem, Shared.BasisChunk003.row3604_mem, Shared.BasisChunk003.row3606_mem, Shared.BasisChunk003.row3607_mem, Shared.BasisChunk003.row3608_mem, Shared.BasisChunk003.row3609_mem, Shared.BasisChunk003.row3610_mem, Shared.BasisChunk003.row3612_mem, Shared.BasisChunk003.row3613_mem, Shared.BasisChunk003.row3614_mem, Shared.BasisChunk003.row3615_mem, Shared.BasisChunk003.row3616_mem, Shared.BasisChunk003.row3617_mem, Shared.BasisChunk003.row3618_mem, Shared.BasisChunk003.row3620_mem, Shared.BasisChunk003.row3621_mem, Shared.BasisChunk003.row3622_mem, Shared.BasisChunk003.row3623_mem, Shared.BasisChunk003.row3624_mem, Shared.BasisChunk003.row3626_mem, Shared.BasisChunk003.row3628_mem, Shared.BasisChunk003.row3630_mem, Shared.BasisChunk003.row3631_mem, Shared.BasisChunk003.row3633_mem, Shared.BasisChunk003.row3634_mem, Shared.BasisChunk003.row3636_mem, Shared.BasisChunk003.row3637_mem, Shared.BasisChunk003.row3638_mem, Shared.BasisChunk003.row3640_mem, Shared.BasisChunk003.row3641_mem, Shared.BasisChunk003.row3642_mem, Shared.BasisChunk003.row3643_mem, Shared.BasisChunk003.row3644_mem, Shared.BasisChunk003.row3645_mem, Shared.BasisChunk003.row3646_mem, Shared.BasisChunk003.row3647_mem, Shared.BasisChunk003.row3648_mem, Shared.BasisChunk003.row3650_mem, Shared.BasisChunk003.row3651_mem, Shared.BasisChunk003.row3652_mem, Shared.BasisChunk003.row3653_mem, Shared.BasisChunk003.row3654_mem, Shared.BasisChunk003.row3655_mem, Shared.BasisChunk003.row3656_mem, Shared.BasisChunk003.row3657_mem, Shared.BasisChunk003.row3658_mem, Shared.BasisChunk003.row3659_mem, Shared.BasisChunk003.row3660_mem, Shared.BasisChunk003.row3661_mem, Shared.BasisChunk003.row3662_mem, Shared.BasisChunk003.row3663_mem, Shared.BasisChunk003.row3666_mem, Shared.BasisChunk003.row3667_mem, Shared.BasisChunk003.row3668_mem, Shared.BasisChunk003.row3669_mem, Shared.BasisChunk003.row3670_mem, Shared.BasisChunk003.row3671_mem, Shared.BasisChunk003.row3672_mem, Shared.BasisChunk003.row3673_mem, Shared.BasisChunk003.row3674_mem, Shared.BasisChunk003.row3676_mem, Shared.BasisChunk003.row3677_mem, Shared.BasisChunk003.row3678_mem, Shared.BasisChunk003.row3680_mem, Shared.BasisChunk003.row3682_mem, Shared.BasisChunk003.row3683_mem, Shared.BasisChunk003.row3685_mem, Shared.BasisChunk003.row3686_mem, Shared.BasisChunk003.row3687_mem, Shared.BasisChunk003.row3689_mem, Shared.BasisChunk003.row3691_mem, Shared.BasisChunk003.row3692_mem, Shared.BasisChunk003.row3694_mem, Shared.BasisChunk003.row3696_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard047
