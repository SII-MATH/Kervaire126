import KIP126.LinProgram.Generated.Naturality.Words200.Shard059
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard059
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard059
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
  exact ⟨Shared.RelationChunk003.relation287_zero, Shared.RelationChunk017.relation824_zero, Shared.RelationChunk017.relation825_zero, Shared.RelationChunk017.relation826_zero, Shared.RelationChunk017.relation827_zero, Shared.RelationChunk017.relation828_zero, Shared.RelationChunk017.relation829_zero, Shared.RelationChunk017.relation830_zero, Shared.RelationChunk017.relation831_zero, Shared.RelationChunk017.relation832_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7554 128 := by cbv
private def targetRows : List BasisRow := [⟨17, 156, 3, "0,6,562,1"⟩,
  ⟨16, 156, 0, "613,1"⟩,
  ⟨16, 156, 1, "9,1,408,1"⟩,
  ⟨16, 156, 2, "0,4,575,1"⟩,
  ⟨15, 156, 1, "0,2,589,1"⟩,
  ⟨14, 156, 1, "1,2,575,1"⟩,
  ⟨13, 156, 2, "2,1,575,1"⟩,
  ⟨12, 156, 0, "8,1,445,1"⟩,
  ⟨12, 156, 2, "2,2,544,1"⟩,
  ⟨12, 156, 4, "0,2,3,1,523,1"⟩,
  ⟨11, 156, 0, "616,1"⟩,
  ⟨11, 156, 1, "615,1"⟩,
  ⟨11, 156, 2, "3,1,544,1"⟩,
  ⟨11, 156, 4, "0,2,3,1,524,1"⟩,
  ⟨10, 156, 0, "15,1,324,1"⟩,
  ⟨10, 156, 1, "13,1,368,1"⟩,
  ⟨10, 156, 2, "1,1,3,1,524,1"⟩,
  ⟨10, 156, 3, "1,2,577,1"⟩,
  ⟨9, 156, 0, "1,1,3,1,525,1"⟩,
  ⟨9, 156, 1, "0,2,7,1,446,1"⟩,
  ⟨8, 156, 0, "1,1,592,1"⟩,
  ⟨8, 156, 1, "1,1,7,1,446,1"⟩,
  ⟨7, 156, 1, "1,1,593,1"⟩,
  ⟨6, 156, 0, "2,1,13,1,324,1"⟩,
  ⟨157, 157, 0, "0,157"⟩,
  ⟨52, 157, 0, "1,1,594,1"⟩,
  ⟨49, 157, 0, "0,1,8,1,431,1"⟩,
  ⟨48, 157, 0, "0,1,16,1,296,1"⟩,
  ⟨47, 157, 0, "0,1,17,1,296,1"⟩,
  ⟨46, 157, 0, "0,1,606,1"⟩,
  ⟨39, 157, 0, "0,1,8,1,432,1"⟩,
  ⟨38, 157, 0, "0,1,8,1,433,1"⟩,
  ⟨38, 157, 1, "0,2,595,1"⟩,
  ⟨37, 157, 0, "0,1,17,1,298,1"⟩,
  ⟨35, 157, 0, "0,7,64,1,137,1"⟩,
  ⟨34, 157, 0, "0,7,64,1,138,1"⟩,
  ⟨31, 157, 1, "0,13,500,1"⟩,
  ⟨30, 157, 0, "0,29,324,1"⟩,
  ⟨29, 157, 0, "0,1,16,1,64,2"⟩,
  ⟨28, 157, 0, "0,1,16,1,299,1"⟩,
  ⟨28, 157, 1, "0,2,64,1,149,1"⟩,
  ⟨28, 157, 2, "0,2,8,2,260,1"⟩,
  ⟨27, 157, 1, "0,2,598,1"⟩,
  ⟨27, 157, 2, "0,2,16,1,292,1"⟩,
  ⟨26, 157, 0, "0,2,17,1,292,1"⟩,
  ⟨25, 157, 0, "0,2,601,1"⟩,
  ⟨25, 157, 1, "0,2,600,1"⟩,
  ⟨24, 157, 1, "0,1,8,3,188,1"⟩,
  ⟨24, 157, 2, "0,3,586,1"⟩,
  ⟨22, 157, 0, "0,3,18,1,278,1"⟩,
  ⟨21, 157, 0, "13,3,133,1"⟩,
  ⟨21, 157, 1, "1,1,603,1"⟩,
  ⟨21, 157, 2, "0,1,608,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4553_mem, Shared.BasisChunk004.row4554_mem, Shared.BasisChunk004.row4555_mem, Shared.BasisChunk004.row4556_mem, Shared.BasisChunk004.row4558_mem, Shared.BasisChunk004.row4560_mem, Shared.BasisChunk004.row4563_mem, Shared.BasisChunk004.row4565_mem, Shared.BasisChunk004.row4567_mem, Shared.BasisChunk004.row4569_mem, Shared.BasisChunk004.row4570_mem, Shared.BasisChunk004.row4571_mem, Shared.BasisChunk004.row4572_mem, Shared.BasisChunk004.row4574_mem, Shared.BasisChunk004.row4575_mem, Shared.BasisChunk004.row4576_mem, Shared.BasisChunk004.row4577_mem, Shared.BasisChunk004.row4578_mem, Shared.BasisChunk004.row4579_mem, Shared.BasisChunk004.row4580_mem, Shared.BasisChunk004.row4581_mem, Shared.BasisChunk004.row4582_mem, Shared.BasisChunk004.row4584_mem, Shared.BasisChunk004.row4585_mem, Shared.BasisChunk004.row4586_mem, Shared.BasisChunk004.row4587_mem, Shared.BasisChunk004.row4588_mem, Shared.BasisChunk004.row4589_mem, Shared.BasisChunk004.row4590_mem, Shared.BasisChunk004.row4591_mem, Shared.BasisChunk004.row4592_mem, Shared.BasisChunk004.row4593_mem, Shared.BasisChunk004.row4594_mem, Shared.BasisChunk004.row4595_mem, Shared.BasisChunk004.row4596_mem, Shared.BasisChunk004.row4597_mem, Shared.BasisChunk004.row4599_mem, Shared.BasisChunk004.row4600_mem, Shared.BasisChunk004.row4601_mem, Shared.BasisChunk004.row4602_mem, Shared.BasisChunk004.row4603_mem, Shared.BasisChunk004.row4604_mem, Shared.BasisChunk004.row4606_mem, Shared.BasisChunk004.row4607_mem, Shared.BasisChunk004.row4608_mem, Shared.BasisChunk004.row4609_mem, Shared.BasisChunk004.row4610_mem, Shared.BasisChunk004.row4612_mem, Shared.BasisChunk004.row4613_mem, Shared.BasisChunk004.row4614_mem, Shared.BasisChunk004.row4615_mem, Shared.BasisChunk004.row4616_mem, Shared.BasisChunk004.row4617_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard059
