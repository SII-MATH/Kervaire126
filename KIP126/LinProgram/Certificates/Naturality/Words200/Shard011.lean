import KIP126.LinProgram.Generated.Naturality.Words200.Shard011
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard011
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard011
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk001.relation173_zero, Shared.RelationChunk001.relation174_zero, Shared.RelationChunk001.relation180_zero, Shared.RelationChunk001.relation183_zero, Shared.RelationChunk001.relation184_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1410 128 := by cbv
private def targetRows : List BasisRow := [⟨8, 85, 0, "134,1"⟩,
  ⟨8, 85, 1, "0,1,129,1"⟩,
  ⟨8, 85, 2, "0,1,128,1"⟩,
  ⟨7, 85, 0, "0,1,130,1"⟩,
  ⟨7, 85, 1, "0,5,7,1,69,1"⟩,
  ⟨6, 85, 0, "0,1,131,1"⟩,
  ⟨5, 85, 1, "0,1,132,1"⟩,
  ⟨4, 85, 0, "0,1,2,1,7,1,69,1"⟩,
  ⟨86, 86, 0, "0,86"⟩,
  ⟨26, 86, 0, "0,2,8,1,71,1"⟩,
  ⟨25, 86, 0, "0,2,16,1,50,1"⟩,
  ⟨24, 86, 0, "0,2,17,1,50,1"⟩,
  ⟨23, 86, 0, "0,22,69,1"⟩,
  ⟨16, 86, 0, "0,2,8,1,72,1"⟩,
  ⟨15, 86, 0, "0,2,127,1"⟩,
  ⟨15, 86, 1, "0,2,126,1"⟩,
  ⟨12, 86, 0, "0,4,120,1"⟩,
  ⟨11, 86, 0, "0,2,3,1,107,1"⟩,
  ⟨10, 86, 0, "0,1,133,1"⟩,
  ⟨9, 86, 0, "0,2,129,1"⟩,
  ⟨9, 86, 1, "0,2,128,1"⟩,
  ⟨8, 86, 1, "0,2,130,1"⟩,
  ⟨8, 86, 2, "0,6,7,1,69,1"⟩,
  ⟨7, 86, 0, "2,1,122,1"⟩,
  ⟨6, 86, 0, "0,1,9,1,69,1"⟩,
  ⟨6, 86, 1, "0,2,132,1"⟩,
  ⟨5, 86, 0, "10,1,69,1"⟩,
  ⟨5, 86, 1, "0,2,2,1,7,1,69,1"⟩,
  ⟨4, 86, 0, "11,1,69,1"⟩,
  ⟨87, 87, 0, "0,87"⟩,
  ⟨25, 87, 0, "0,3,17,1,50,1"⟩,
  ⟨24, 87, 1, "0,23,69,1"⟩,
  ⟨23, 87, 0, "8,1,78,1"⟩,
  ⟨22, 87, 0, "17,1,56,1"⟩,
  ⟨21, 87, 0, "136,1"⟩,
  ⟨20, 87, 0, "8,3,19,1"⟩,
  ⟨19, 87, 0, "8,3,20,1"⟩,
  ⟨18, 87, 1, "8,2,45,1"⟩,
  ⟨17, 87, 0, "138,1"⟩,
  ⟨17, 87, 1, "8,2,46,1"⟩,
  ⟨16, 87, 0, "8,1,9,1,13,2"⟩,
  ⟨15, 87, 0, "9,1,13,1,32,1"⟩,
  ⟨13, 87, 0, "8,1,80,1"⟩,
  ⟨10, 87, 0, "0,3,128,1"⟩,
  ⟨9, 87, 1, "0,7,7,1,69,1"⟩,
  ⟨8, 87, 1, "0,1,2,1,122,1"⟩,
  ⟨7, 87, 0, "0,2,9,1,69,1"⟩,
  ⟨6, 87, 0, "0,1,10,1,69,1"⟩,
  ⟨88, 88, 0, "0,88"⟩,
  ⟨29, 88, 0, "140,1"⟩,
  ⟨26, 88, 0, "0,4,17,1,50,1"⟩,
  ⟨25, 88, 0, "0,1,8,1,77,1"⟩,
  ⟨25, 88, 1, "0,24,69,1"⟩,
  ⟨24, 88, 0, "0,1,8,1,78,1"⟩,
  ⟨23, 88, 0, "0,1,17,1,56,1"⟩,
  ⟨19, 88, 0, "0,1,137,1"⟩,
  ⟨18, 88, 0, "0,1,138,1"⟩,
  ⟨15, 88, 0, "0,1,8,1,79,1"⟩,
  ⟨14, 88, 0, "2,1,126,1"⟩,
  ⟨14, 88, 1, "0,1,8,1,80,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row850_mem, Shared.BasisChunk000.row851_mem, Shared.BasisChunk000.row852_mem, Shared.BasisChunk000.row853_mem, Shared.BasisChunk000.row854_mem, Shared.BasisChunk000.row855_mem, Shared.BasisChunk000.row857_mem, Shared.BasisChunk000.row858_mem, Shared.BasisChunk000.row859_mem, Shared.BasisChunk000.row861_mem, Shared.BasisChunk000.row862_mem, Shared.BasisChunk000.row863_mem, Shared.BasisChunk000.row864_mem, Shared.BasisChunk000.row866_mem, Shared.BasisChunk000.row867_mem, Shared.BasisChunk000.row868_mem, Shared.BasisChunk000.row869_mem, Shared.BasisChunk000.row870_mem, Shared.BasisChunk000.row871_mem, Shared.BasisChunk000.row872_mem, Shared.BasisChunk000.row873_mem, Shared.BasisChunk000.row875_mem, Shared.BasisChunk000.row876_mem, Shared.BasisChunk000.row877_mem, Shared.BasisChunk000.row879_mem, Shared.BasisChunk000.row880_mem, Shared.BasisChunk000.row881_mem, Shared.BasisChunk000.row882_mem, Shared.BasisChunk000.row883_mem, Shared.BasisChunk000.row884_mem, Shared.BasisChunk000.row885_mem, Shared.BasisChunk000.row887_mem, Shared.BasisChunk000.row888_mem, Shared.BasisChunk000.row889_mem, Shared.BasisChunk000.row890_mem, Shared.BasisChunk000.row891_mem, Shared.BasisChunk000.row892_mem, Shared.BasisChunk000.row894_mem, Shared.BasisChunk000.row895_mem, Shared.BasisChunk000.row896_mem, Shared.BasisChunk000.row897_mem, Shared.BasisChunk000.row898_mem, Shared.BasisChunk000.row900_mem, Shared.BasisChunk000.row901_mem, Shared.BasisChunk000.row903_mem, Shared.BasisChunk000.row905_mem, Shared.BasisChunk000.row906_mem, Shared.BasisChunk000.row907_mem, Shared.BasisChunk000.row908_mem, Shared.BasisChunk000.row910_mem, Shared.BasisChunk000.row911_mem, Shared.BasisChunk000.row912_mem, Shared.BasisChunk000.row913_mem, Shared.BasisChunk000.row914_mem, Shared.BasisChunk000.row915_mem, Shared.BasisChunk000.row916_mem, Shared.BasisChunk000.row917_mem, Shared.BasisChunk000.row918_mem, Shared.BasisChunk000.row919_mem, Shared.BasisChunk000.row920_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard011
