import KIP126.LinProgram.Generated.Naturality.Words200.Shard063
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard063
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard063
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
  exact ⟨Shared.RelationChunk000.relation18_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation228_zero, Shared.RelationChunk004.relation304_zero, Shared.RelationChunk010.relation538_zero, Shared.RelationChunk019.relation891_zero, Shared.RelationChunk019.relation907_zero, Shared.RelationChunk019.relation908_zero, Shared.RelationChunk019.relation909_zero, Shared.RelationChunk019.relation911_zero, Shared.RelationChunk019.relation912_zero, Shared.RelationChunk019.relation913_zero, Shared.RelationChunk019.relation914_zero, Shared.RelationChunk019.relation915_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8066 128 := by cbv
private def targetRows : List BasisRow := [⟨34, 160, 0, "0,16,500,1"⟩,
  ⟨33, 160, 0, "0,32,324,1"⟩,
  ⟨32, 160, 0, "0,2,623,1"⟩,
  ⟨31, 160, 0, "0,1,637,1"⟩,
  ⟨31, 160, 1, "0,5,64,1,149,1"⟩,
  ⟨30, 160, 0, "0,5,598,1"⟩,
  ⟨29, 160, 0, "0,5,17,1,292,1"⟩,
  ⟨28, 160, 0, "0,2,8,2,278,1"⟩,
  ⟨28, 160, 1, "0,5,601,1"⟩,
  ⟨28, 160, 2, "0,5,600,1"⟩,
  ⟨27, 160, 0, "0,2,8,1,454,1"⟩,
  ⟨27, 160, 1, "0,6,586,1"⟩,
  ⟨23, 160, 0, "13,4,67,1"⟩,
  ⟨22, 160, 0, "643,1"⟩,
  ⟨22, 160, 1, "9,1,13,3,75,1"⟩,
  ⟨22, 160, 2, "0,2,627,1"⟩,
  ⟨21, 160, 0, "645,1"⟩,
  ⟨20, 160, 1, "0,2,628,1"⟩,
  ⟨20, 160, 2, "0,8,575,1"⟩,
  ⟨19, 160, 2, "0,3,17,1,314,1"⟩,
  ⟨18, 160, 0, "647,1"⟩,
  ⟨18, 160, 1, "8,1,69,1,113,1"⟩,
  ⟨18, 160, 2, "0,1,8,1,475,1"⟩,
  ⟨18, 160, 3, "0,2,629,1"⟩,
  ⟨17, 160, 1, "13,1,417,1"⟩,
  ⟨17, 160, 2, "8,1,483,1"⟩,
  ⟨17, 160, 4, "0,1,17,1,333,1"⟩,
  ⟨16, 160, 0, "649,1"⟩,
  ⟨16, 160, 2, "17,1,338,1"⟩,
  ⟨15, 160, 0, "650,1"⟩,
  ⟨15, 160, 1, "8,1,486,1"⟩,
  ⟨14, 160, 0, "651,1"⟩,
  ⟨14, 160, 1, "9,1,450,1"⟩,
  ⟨13, 160, 0, "1,1,7,1,486,1"⟩,
  ⟨13, 160, 1, "0,2,631,1"⟩,
  ⟨12, 160, 1, "1,1,631,1"⟩,
  ⟨12, 160, 2, "0,1,18,1,311,1"⟩,
  ⟨12, 160, 3, "0,1,7,2,314,1"⟩,
  ⟨11, 160, 2, "1,1,16,1,69,2"⟩,
  ⟨11, 160, 3, "0,1,18,1,314,1"⟩,
  ⟨11, 160, 4, "0,2,17,1,69,2"⟩,
  ⟨11, 160, 5, "0,2,16,1,324,1"⟩,
  ⟨10, 160, 0, "68,1,163,1"⟩,
  ⟨10, 160, 3, "0,2,17,1,324,1"⟩,
  ⟨9, 160, 0, "3,1,577,1"⟩,
  ⟨8, 160, 0, "2,1,617,1"⟩,
  ⟨7, 160, 0, "2,2,13,1,324,1"⟩,
  ⟨6, 160, 0, "7,1,507,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4852_mem, Shared.BasisChunk004.row4853_mem, Shared.BasisChunk004.row4854_mem, Shared.BasisChunk004.row4855_mem, Shared.BasisChunk004.row4856_mem, Shared.BasisChunk004.row4857_mem, Shared.BasisChunk004.row4858_mem, Shared.BasisChunk004.row4859_mem, Shared.BasisChunk004.row4860_mem, Shared.BasisChunk004.row4861_mem, Shared.BasisChunk004.row4862_mem, Shared.BasisChunk004.row4863_mem, Shared.BasisChunk004.row4865_mem, Shared.BasisChunk004.row4867_mem, Shared.BasisChunk004.row4868_mem, Shared.BasisChunk004.row4869_mem, Shared.BasisChunk004.row4870_mem, Shared.BasisChunk004.row4874_mem, Shared.BasisChunk004.row4875_mem, Shared.BasisChunk004.row4878_mem, Shared.BasisChunk004.row4879_mem, Shared.BasisChunk004.row4880_mem, Shared.BasisChunk004.row4881_mem, Shared.BasisChunk004.row4882_mem, Shared.BasisChunk004.row4884_mem, Shared.BasisChunk004.row4885_mem, Shared.BasisChunk004.row4887_mem, Shared.BasisChunk004.row4888_mem, Shared.BasisChunk004.row4890_mem, Shared.BasisChunk004.row4891_mem, Shared.BasisChunk004.row4892_mem, Shared.BasisChunk004.row4893_mem, Shared.BasisChunk004.row4894_mem, Shared.BasisChunk004.row4895_mem, Shared.BasisChunk004.row4896_mem, Shared.BasisChunk004.row4898_mem, Shared.BasisChunk004.row4899_mem, Shared.BasisChunk004.row4900_mem, Shared.BasisChunk004.row4903_mem, Shared.BasisChunk004.row4904_mem, Shared.BasisChunk004.row4905_mem, Shared.BasisChunk004.row4906_mem, Shared.BasisChunk004.row4907_mem, Shared.BasisChunk004.row4910_mem, Shared.BasisChunk004.row4911_mem, Shared.BasisChunk004.row4912_mem, Shared.BasisChunk004.row4913_mem, Shared.BasisChunk004.row4914_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard063
