import KIP126.LinProgram.Generated.Naturality.Words200.Shard060
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard060
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard060
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
  exact ⟨Shared.RelationChunk000.relation17_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation71_zero, Shared.RelationChunk000.relation72_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk001.relation203_zero, Shared.RelationChunk002.relation213_zero, Shared.RelationChunk007.relation413_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk008.relation459_zero, Shared.RelationChunk008.relation471_zero, Shared.RelationChunk008.relation472_zero, Shared.RelationChunk010.relation546_zero, Shared.RelationChunk010.relation550_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation553_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk010.relation555_zero, Shared.RelationChunk010.relation556_zero, Shared.RelationChunk010.relation557_zero, Shared.RelationChunk010.relation558_zero, Shared.RelationChunk010.relation559_zero, Shared.RelationChunk010.relation560_zero, Shared.RelationChunk010.relation561_zero, Shared.RelationChunk017.relation855_zero, Shared.RelationChunk017.relation856_zero, Shared.RelationChunk018.relation857_zero, Shared.RelationChunk018.relation858_zero, Shared.RelationChunk018.relation859_zero, Shared.RelationChunk018.relation860_zero, Shared.RelationChunk018.relation861_zero, Shared.RelationChunk018.relation868_zero, Shared.RelationChunk018.relation869_zero, Shared.RelationChunk018.relation870_zero, Shared.RelationChunk018.relation871_zero, Shared.RelationChunk018.relation872_zero, Shared.RelationChunk018.relation873_zero, Shared.RelationChunk018.relation876_zero, Shared.RelationChunk018.relation877_zero, Shared.RelationChunk018.relation878_zero, Shared.RelationChunk018.relation879_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7682 128 := by cbv
private def targetRows : List BasisRow := [⟨20, 157, 0, "13,3,134,1"⟩,
  ⟨20, 157, 1, "1,1,42,1,209,1"⟩,
  ⟨20, 157, 2, "0,1,609,1"⟩,
  ⟨19, 157, 1, "0,1,610,1"⟩,
  ⟨18, 157, 0, "8,1,449,1"⟩,
  ⟨18, 157, 1, "0,1,612,1"⟩,
  ⟨18, 157, 2, "0,7,562,1"⟩,
  ⟨17, 157, 0, "16,1,314,1"⟩,
  ⟨17, 157, 2, "0,1,613,1"⟩,
  ⟨17, 157, 3, "0,5,575,1"⟩,
  ⟨16, 157, 2, "17,1,314,1"⟩,
  ⟨16, 157, 3, "0,3,589,1"⟩,
  ⟨15, 157, 0, "619,1"⟩,
  ⟨15, 157, 1, "8,1,18,1,209,1"⟩,
  ⟨15, 157, 2, "0,1,3,1,540,1"⟩,
  ⟨14, 157, 0, "620,1"⟩,
  ⟨14, 157, 1, "8,1,450,1"⟩,
  ⟨14, 157, 2, "0,1,8,1,443,1"⟩,
  ⟨14, 157, 3, "0,1,2,1,575,1"⟩,
  ⟨13, 157, 1, "13,1,373,1"⟩,
  ⟨13, 157, 2, "0,1,8,1,445,1"⟩,
  ⟨13, 157, 3, "0,1,3,1,543,1"⟩,
  ⟨12, 157, 1, "0,1,615,1"⟩,
  ⟨12, 157, 2, "0,1,3,1,544,1"⟩,
  ⟨11, 157, 1, "1,1,13,1,69,1,76,1"⟩,
  ⟨11, 157, 2, "0,1,15,1,324,1"⟩,
  ⟨10, 157, 1, "0,3,7,1,446,1"⟩,
  ⟨9, 157, 0, "7,1,480,1"⟩,
  ⟨8, 157, 0, "0,1,617,1"⟩,
  ⟨7, 157, 0, "1,1,605,1"⟩,
  ⟨7, 157, 1, "0,1,2,1,13,1,324,1"⟩,
  ⟨6, 157, 0, "1,1,4,1,7,1,324,1"⟩,
  ⟨158, 158, 0, "0,158"⟩,
  ⟨50, 158, 0, "0,2,8,1,431,1"⟩,
  ⟨49, 158, 0, "0,2,16,1,296,1"⟩,
  ⟨48, 158, 0, "0,2,17,1,296,1"⟩,
  ⟨47, 158, 0, "0,2,606,1"⟩,
  ⟨40, 158, 0, "0,2,8,1,432,1"⟩,
  ⟨39, 158, 0, "0,2,8,1,433,1"⟩,
  ⟨39, 158, 1, "0,3,595,1"⟩,
  ⟨35, 158, 0, "0,8,64,1,138,1"⟩,
  ⟨34, 158, 0, "31,1,245,1"⟩,
  ⟨33, 158, 0, "8,1,453,1"⟩,
  ⟨32, 158, 0, "8,2,16,1,149,1"⟩,
  ⟨32, 158, 1, "0,14,500,1"⟩,
  ⟨31, 158, 0, "8,2,17,1,149,1"⟩,
  ⟨31, 158, 1, "0,30,324,1"⟩,
  ⟨30, 158, 1, "8,2,277,1"⟩,
  ⟨29, 158, 0, "8,3,193,1"⟩,
  ⟨29, 158, 1, "0,2,16,1,299,1"⟩,
  ⟨29, 158, 2, "0,3,64,1,149,1"⟩,
  ⟨28, 158, 0, "8,3,194,1"⟩,
  ⟨28, 158, 1, "0,3,598,1"⟩,
  ⟨27, 158, 0, "8,2,13,1,167,1"⟩,
  ⟨27, 158, 1, "0,3,17,1,292,1"⟩,
  ⟨26, 158, 1, "8,1,13,1,248,1"⟩,
  ⟨26, 158, 3, "0,3,601,1"⟩,
  ⟨26, 158, 4, "0,3,600,1"⟩,
  ⟨25, 158, 0, "624,1"⟩,
  ⟨25, 158, 1, "13,2,219,1"⟩,
  ⟨25, 158, 2, "8,1,454,1"⟩,
  ⟨25, 158, 3, "0,4,586,1"⟩,
  ⟨24, 158, 0, "20,1,292,1"⟩,
  ⟨24, 158, 1, "13,2,220,1"⟩,
  ⟨24, 158, 2, "8,1,455,1"⟩,
  ⟨23, 158, 0, "625,1"⟩,
  ⟨23, 158, 1, "9,1,420,1"⟩,
  ⟨23, 158, 2, "2,1,585,1"⟩,
  ⟨23, 158, 3, "1,2,586,1"⟩,
  ⟨22, 158, 1, "8,2,279,1"⟩,
  ⟨22, 158, 2, "0,2,608,1"⟩,
  ⟨21, 158, 0, "8,2,280,1"⟩,
  ⟨21, 158, 1, "0,2,609,1"⟩,
  ⟨20, 158, 1, "8,1,9,1,261,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4618_mem, Shared.BasisChunk004.row4619_mem, Shared.BasisChunk004.row4620_mem, Shared.BasisChunk004.row4622_mem, Shared.BasisChunk004.row4623_mem, Shared.BasisChunk004.row4624_mem, Shared.BasisChunk004.row4625_mem, Shared.BasisChunk004.row4626_mem, Shared.BasisChunk004.row4628_mem, Shared.BasisChunk004.row4629_mem, Shared.BasisChunk004.row4632_mem, Shared.BasisChunk004.row4633_mem, Shared.BasisChunk004.row4634_mem, Shared.BasisChunk004.row4635_mem, Shared.BasisChunk004.row4636_mem, Shared.BasisChunk004.row4637_mem, Shared.BasisChunk004.row4638_mem, Shared.BasisChunk004.row4639_mem, Shared.BasisChunk004.row4640_mem, Shared.BasisChunk004.row4642_mem, Shared.BasisChunk004.row4643_mem, Shared.BasisChunk004.row4644_mem, Shared.BasisChunk004.row4646_mem, Shared.BasisChunk004.row4647_mem, Shared.BasisChunk004.row4649_mem, Shared.BasisChunk004.row4650_mem, Shared.BasisChunk004.row4652_mem, Shared.BasisChunk004.row4653_mem, Shared.BasisChunk004.row4654_mem, Shared.BasisChunk004.row4655_mem, Shared.BasisChunk004.row4656_mem, Shared.BasisChunk004.row4657_mem, Shared.BasisChunk004.row4658_mem, Shared.BasisChunk004.row4660_mem, Shared.BasisChunk004.row4661_mem, Shared.BasisChunk004.row4662_mem, Shared.BasisChunk004.row4663_mem, Shared.BasisChunk004.row4665_mem, Shared.BasisChunk004.row4666_mem, Shared.BasisChunk004.row4667_mem, Shared.BasisChunk004.row4669_mem, Shared.BasisChunk004.row4670_mem, Shared.BasisChunk004.row4671_mem, Shared.BasisChunk004.row4672_mem, Shared.BasisChunk004.row4673_mem, Shared.BasisChunk004.row4674_mem, Shared.BasisChunk004.row4675_mem, Shared.BasisChunk004.row4677_mem, Shared.BasisChunk004.row4678_mem, Shared.BasisChunk004.row4679_mem, Shared.BasisChunk004.row4680_mem, Shared.BasisChunk004.row4681_mem, Shared.BasisChunk004.row4682_mem, Shared.BasisChunk004.row4683_mem, Shared.BasisChunk004.row4684_mem, Shared.BasisChunk004.row4686_mem, Shared.BasisChunk004.row4688_mem, Shared.BasisChunk004.row4689_mem, Shared.BasisChunk004.row4690_mem, Shared.BasisChunk004.row4691_mem, Shared.BasisChunk004.row4692_mem, Shared.BasisChunk004.row4693_mem, Shared.BasisChunk004.row4694_mem, Shared.BasisChunk004.row4695_mem, Shared.BasisChunk004.row4696_mem, Shared.BasisChunk004.row4697_mem, Shared.BasisChunk004.row4698_mem, Shared.BasisChunk004.row4699_mem, Shared.BasisChunk004.row4700_mem, Shared.BasisChunk004.row4702_mem, Shared.BasisChunk004.row4703_mem, Shared.BasisChunk004.row4704_mem, Shared.BasisChunk004.row4705_mem, Shared.BasisChunk004.row4707_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard060
