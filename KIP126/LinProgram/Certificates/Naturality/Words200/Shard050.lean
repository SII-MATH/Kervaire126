import KIP126.LinProgram.Generated.Naturality.Words200.Shard050
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard050
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard050
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation2_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation44_zero, Shared.RelationChunk000.relation52_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk001.relation140_zero, Shared.RelationChunk001.relation160_zero, Shared.RelationChunk001.relation164_zero, Shared.RelationChunk001.relation166_zero, Shared.RelationChunk001.relation172_zero, Shared.RelationChunk008.relation446_zero, Shared.RelationChunk008.relation447_zero, Shared.RelationChunk008.relation448_zero, Shared.RelationChunk012.relation620_zero, Shared.RelationChunk012.relation645_zero, Shared.RelationChunk012.relation652_zero, Shared.RelationChunk013.relation691_zero, Shared.RelationChunk013.relation692_zero, Shared.RelationChunk013.relation693_zero, Shared.RelationChunk013.relation694_zero, Shared.RelationChunk013.relation695_zero, Shared.RelationChunk013.relation696_zero, Shared.RelationChunk013.relation697_zero, Shared.RelationChunk014.relation705_zero, Shared.RelationChunk014.relation706_zero, Shared.RelationChunk014.relation707_zero, Shared.RelationChunk014.relation708_zero, Shared.RelationChunk014.relation709_zero, Shared.RelationChunk014.relation710_zero, Shared.RelationChunk014.relation711_zero, Shared.RelationChunk014.relation712_zero, Shared.RelationChunk014.relation713_zero, Shared.RelationChunk014.relation717_zero, Shared.RelationChunk014.relation718_zero, Shared.RelationChunk014.relation719_zero, Shared.RelationChunk014.relation720_zero, Shared.RelationChunk014.relation721_zero, Shared.RelationChunk014.relation722_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6402 128 := by cbv
private def targetRows : List BasisRow := [⟨13, 148, 3, "0,1,43,1,174,1"⟩,
  ⟨13, 148, 4, "0,1,7,1,351,1"⟩,
  ⟨13, 148, 5, "0,3,7,1,333,1"⟩,
  ⟨12, 148, 0, "542,1"⟩,
  ⟨12, 148, 2, "0,2,521,1"⟩,
  ⟨11, 148, 1, "3,1,463,1"⟩,
  ⟨11, 148, 2, "0,1,3,2,352,1"⟩,
  ⟨11, 148, 3, "0,2,523,1"⟩,
  ⟨10, 148, 2, "1,1,523,1"⟩,
  ⟨10, 148, 3, "0,1,7,1,352,1"⟩,
  ⟨10, 148, 4, "0,2,524,1"⟩,
  ⟨9, 148, 1, "7,1,367,1"⟩,
  ⟨9, 148, 2, "1,1,524,1"⟩,
  ⟨9, 148, 3, "0,4,506,1"⟩,
  ⟨8, 148, 2, "1,1,525,1"⟩,
  ⟨8, 148, 3, "0,2,8,1,69,2"⟩,
  ⟨7, 148, 0, "7,1,368,1"⟩,
  ⟨7, 148, 2, "1,2,506,1"⟩,
  ⟨7, 148, 3, "0,2,526,1"⟩,
  ⟨7, 148, 4, "0,2,8,1,324,1"⟩,
  ⟨6, 148, 0, "2,1,506,1"⟩,
  ⟨6, 148, 2, "0,4,7,1,324,1"⟩,
  ⟨4, 148, 0, "548,1"⟩,
  ⟨3, 148, 0, "2,1,7,1,324,1"⟩,
  ⟨149, 149, 0, "0,149"⟩,
  ⟨50, 149, 0, "0,1,536,1"⟩,
  ⟨46, 149, 0, "0,2,8,1,325,1"⟩,
  ⟨45, 149, 0, "0,2,8,1,326,1"⟩,
  ⟨36, 149, 0, "0,2,8,2,224,1"⟩,
  ⟨35, 149, 0, "0,2,8,2,225,1"⟩,
  ⟨34, 149, 0, "0,3,17,1,244,1"⟩,
  ⟨33, 149, 0, "0,2,17,2,138,1"⟩,
  ⟨32, 149, 2, "0,6,491,1"⟩,
  ⟨31, 149, 0, "17,1,257,1"⟩,
  ⟨31, 149, 1, "0,4,509,1"⟩,
  ⟨30, 149, 0, "8,1,344,1"⟩,
  ⟨29, 149, 0, "8,1,345,1"⟩,
  ⟨29, 149, 1, "0,3,516,1"⟩,
  ⟨28, 149, 0, "8,3,160,1"⟩,
  ⟨27, 149, 0, "8,2,232,1"⟩,
  ⟨26, 149, 1, "8,2,233,1"⟩,
  ⟨25, 149, 0, "17,1,260,1"⟩,
  ⟨25, 149, 1, "8,1,9,1,219,1"⟩,
  ⟨25, 149, 2, "0,11,440,1"⟩,
  ⟨24, 149, 0, "9,1,13,1,194,1"⟩,
  ⟨23, 149, 1, "0,5,500,1"⟩,
  ⟨22, 149, 2, "0,21,324,1"⟩,
  ⟨21, 149, 1, "13,1,292,1"⟩,
  ⟨20, 149, 0, "551,1"⟩,
  ⟨20, 149, 1, "8,1,348,1"⟩,
  ⟨19, 149, 0, "8,1,350,1"⟩,
  ⟨19, 149, 1, "0,1,539,1"⟩,
  ⟨18, 149, 0, "8,1,13,1,209,1"⟩,
  ⟨18, 149, 1, "1,1,13,1,287,1"⟩,
  ⟨17, 149, 0, "13,1,294,1"⟩,
  ⟨17, 149, 1, "2,1,7,1,328,1"⟩,
  ⟨16, 149, 1, "13,2,181,1"⟩,
  ⟨16, 149, 2, "0,1,8,1,69,1,72,1"⟩,
  ⟨16, 149, 3, "0,6,7,1,314,1"⟩,
  ⟨15, 149, 0, "8,1,351,1"⟩,
  ⟨15, 149, 1, "1,1,531,1"⟩,
  ⟨15, 149, 2, "0,1,8,1,337,1"⟩,
  ⟨15, 149, 3, "0,1,3,2,363,1"⟩,
  ⟨15, 149, 4, "0,2,533,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3837_mem, Shared.BasisChunk003.row3838_mem, Shared.BasisChunk003.row3839_mem, Shared.BasisChunk003.row3840_mem, Shared.BasisChunk003.row3842_mem, Shared.BasisChunk003.row3844_mem, Shared.BasisChunk003.row3845_mem, Shared.BasisChunk003.row3846_mem, Shared.BasisChunk003.row3849_mem, Shared.BasisChunk003.row3850_mem, Shared.BasisChunk003.row3851_mem, Shared.BasisChunk003.row3853_mem, Shared.BasisChunk003.row3854_mem, Shared.BasisChunk003.row3855_mem, Shared.BasisChunk003.row3858_mem, Shared.BasisChunk003.row3859_mem, Shared.BasisChunk003.row3860_mem, Shared.BasisChunk003.row3862_mem, Shared.BasisChunk003.row3863_mem, Shared.BasisChunk003.row3864_mem, Shared.BasisChunk003.row3865_mem, Shared.BasisChunk003.row3867_mem, Shared.BasisChunk003.row3869_mem, Shared.BasisChunk003.row3871_mem, Shared.BasisChunk003.row3872_mem, Shared.BasisChunk003.row3873_mem, Shared.BasisChunk003.row3874_mem, Shared.BasisChunk003.row3875_mem, Shared.BasisChunk003.row3877_mem, Shared.BasisChunk003.row3878_mem, Shared.BasisChunk003.row3879_mem, Shared.BasisChunk003.row3880_mem, Shared.BasisChunk003.row3883_mem, Shared.BasisChunk003.row3884_mem, Shared.BasisChunk003.row3885_mem, Shared.BasisChunk003.row3886_mem, Shared.BasisChunk003.row3887_mem, Shared.BasisChunk003.row3888_mem, Shared.BasisChunk003.row3889_mem, Shared.BasisChunk003.row3890_mem, Shared.BasisChunk003.row3892_mem, Shared.BasisChunk003.row3893_mem, Shared.BasisChunk003.row3894_mem, Shared.BasisChunk003.row3895_mem, Shared.BasisChunk003.row3896_mem, Shared.BasisChunk003.row3898_mem, Shared.BasisChunk003.row3901_mem, Shared.BasisChunk003.row3903_mem, Shared.BasisChunk003.row3904_mem, Shared.BasisChunk003.row3905_mem, Shared.BasisChunk003.row3906_mem, Shared.BasisChunk003.row3907_mem, Shared.BasisChunk003.row3908_mem, Shared.BasisChunk003.row3909_mem, Shared.BasisChunk003.row3910_mem, Shared.BasisChunk003.row3911_mem, Shared.BasisChunk003.row3913_mem, Shared.BasisChunk003.row3914_mem, Shared.BasisChunk003.row3915_mem, Shared.BasisChunk003.row3916_mem, Shared.BasisChunk003.row3917_mem, Shared.BasisChunk003.row3918_mem, Shared.BasisChunk003.row3919_mem, Shared.BasisChunk003.row3920_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard050
