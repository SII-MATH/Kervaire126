import KIP126.LinProgram.Generated.Naturality.Words200.Shard008
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard008
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard008
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
  exact ⟨Shared.RelationChunk000.relation3_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation126_zero, Shared.RelationChunk000.relation139_zero, Shared.RelationChunk001.relation142_zero, Shared.RelationChunk001.relation143_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1026 128 := by cbv
private def targetRows : List BasisRow := [⟨7, 75, 0, "3,1,74,1"⟩,
  ⟨7, 75, 1, "2,2,76,1"⟩,
  ⟨6, 75, 1, "0,2,96,1"⟩,
  ⟨5, 75, 1, "0,3,3,1,69,1"⟩,
  ⟨76, 76, 0, "0,76"⟩,
  ⟨25, 76, 0, "102,1"⟩,
  ⟨21, 76, 0, "0,1,8,1,55,1"⟩,
  ⟨20, 76, 0, "0,1,8,1,56,1"⟩,
  ⟨19, 76, 0, "0,1,17,1,40,1"⟩,
  ⟨14, 76, 0, "0,4,90,1"⟩,
  ⟨13, 76, 0, "0,12,69,1"⟩,
  ⟨11, 76, 1, "0,1,101,1"⟩,
  ⟨10, 76, 0, "104,1"⟩,
  ⟨10, 76, 1, "103,1"⟩,
  ⟨9, 76, 0, "106,1"⟩,
  ⟨8, 76, 1, "0,1,3,1,74,1"⟩,
  ⟨7, 76, 0, "0,3,96,1"⟩,
  ⟨6, 76, 0, "2,1,92,1"⟩,
  ⟨5, 76, 0, "1,1,99,1"⟩,
  ⟨4, 76, 0, "1,2,3,1,69,1"⟩,
  ⟨77, 77, 0, "0,77"⟩,
  ⟨26, 77, 0, "0,1,102,1"⟩,
  ⟨22, 77, 0, "0,2,8,1,55,1"⟩,
  ⟨21, 77, 0, "0,2,8,1,56,1"⟩,
  ⟨15, 77, 1, "0,5,90,1"⟩,
  ⟨14, 77, 0, "0,13,69,1"⟩,
  ⟨12, 77, 0, "18,1,40,1"⟩,
  ⟨12, 77, 1, "0,2,101,1"⟩,
  ⟨11, 77, 0, "0,1,104,1"⟩,
  ⟨11, 77, 1, "0,1,103,1"⟩,
  ⟨10, 77, 0, "0,1,106,1"⟩,
  ⟨9, 77, 0, "0,1,107,1"⟩,
  ⟨8, 77, 1, "2,1,95,1"⟩,
  ⟨7, 77, 0, "1,1,3,1,76,1"⟩,
  ⟨7, 77, 1, "0,1,2,1,92,1"⟩,
  ⟨6, 77, 0, "109,1"⟩,
  ⟨6, 77, 1, "1,2,96,1"⟩,
  ⟨5, 77, 0, "1,1,4,1,69,1"⟩,
  ⟨78, 78, 0, "0,78"⟩,
  ⟨27, 78, 0, "0,2,102,1"⟩,
  ⟨23, 78, 0, "111,1"⟩,
  ⟨19, 78, 0, "8,1,16,1,17,1"⟩,
  ⟨18, 78, 0, "8,1,17,2"⟩,
  ⟨17, 78, 0, "8,1,60,1"⟩,
  ⟨16, 78, 0, "8,3,13,1"⟩,
  ⟨16, 78, 1, "0,6,90,1"⟩,
  ⟨15, 78, 0, "8,2,32,1"⟩,
  ⟨15, 78, 1, "0,14,69,1"⟩,
  ⟨14, 78, 1, "8,1,13,1,23,1"⟩,
  ⟨13, 78, 0, "113,1"⟩,
  ⟨13, 78, 1, "13,1,51,1"⟩,
  ⟨12, 78, 0, "13,1,52,1"⟩,
  ⟨12, 78, 1, "0,2,103,1"⟩,
  ⟨11, 78, 0, "114,1"⟩,
  ⟨11, 78, 1, "0,2,106,1"⟩,
  ⟨10, 78, 0, "1,1,105,1"⟩,
  ⟨10, 78, 1, "0,2,107,1"⟩,
  ⟨9, 78, 1, "0,1,2,1,95,1"⟩,
  ⟨8, 78, 0, "3,1,84,1"⟩,
  ⟨7, 78, 0, "0,1,109,1"⟩,
  ⟨79, 79, 0, "0,79"⟩,
  ⟨25, 79, 0, "0,1,110,1"⟩,
  ⟨24, 79, 0, "0,1,111,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row619_mem, Shared.BasisChunk000.row620_mem, Shared.BasisChunk000.row622_mem, Shared.BasisChunk000.row624_mem, Shared.BasisChunk000.row626_mem, Shared.BasisChunk000.row628_mem, Shared.BasisChunk000.row629_mem, Shared.BasisChunk000.row630_mem, Shared.BasisChunk000.row631_mem, Shared.BasisChunk000.row632_mem, Shared.BasisChunk000.row633_mem, Shared.BasisChunk000.row635_mem, Shared.BasisChunk000.row636_mem, Shared.BasisChunk000.row637_mem, Shared.BasisChunk000.row638_mem, Shared.BasisChunk000.row641_mem, Shared.BasisChunk000.row642_mem, Shared.BasisChunk000.row643_mem, Shared.BasisChunk000.row644_mem, Shared.BasisChunk000.row645_mem, Shared.BasisChunk000.row646_mem, Shared.BasisChunk000.row647_mem, Shared.BasisChunk000.row648_mem, Shared.BasisChunk000.row649_mem, Shared.BasisChunk000.row651_mem, Shared.BasisChunk000.row652_mem, Shared.BasisChunk000.row653_mem, Shared.BasisChunk000.row654_mem, Shared.BasisChunk000.row655_mem, Shared.BasisChunk000.row656_mem, Shared.BasisChunk000.row657_mem, Shared.BasisChunk000.row658_mem, Shared.BasisChunk000.row660_mem, Shared.BasisChunk000.row661_mem, Shared.BasisChunk000.row662_mem, Shared.BasisChunk000.row663_mem, Shared.BasisChunk000.row664_mem, Shared.BasisChunk000.row665_mem, Shared.BasisChunk000.row666_mem, Shared.BasisChunk000.row667_mem, Shared.BasisChunk000.row669_mem, Shared.BasisChunk000.row671_mem, Shared.BasisChunk000.row672_mem, Shared.BasisChunk000.row673_mem, Shared.BasisChunk000.row674_mem, Shared.BasisChunk000.row675_mem, Shared.BasisChunk000.row676_mem, Shared.BasisChunk000.row677_mem, Shared.BasisChunk000.row679_mem, Shared.BasisChunk000.row680_mem, Shared.BasisChunk000.row681_mem, Shared.BasisChunk000.row682_mem, Shared.BasisChunk000.row683_mem, Shared.BasisChunk000.row684_mem, Shared.BasisChunk000.row685_mem, Shared.BasisChunk000.row686_mem, Shared.BasisChunk000.row687_mem, Shared.BasisChunk000.row689_mem, Shared.BasisChunk000.row690_mem, Shared.BasisChunk000.row691_mem, Shared.BasisChunk000.row693_mem, Shared.BasisChunk000.row694_mem, Shared.BasisChunk000.row695_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard008
