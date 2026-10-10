import KIP126.LinProgram.Generated.Naturality.Words200.Shard067
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard067
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard067
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
  exact ⟨Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk002.relation236_zero, Shared.RelationChunk012.relation643_zero, Shared.RelationChunk020.relation938_zero, Shared.RelationChunk021.relation957_zero, Shared.RelationChunk021.relation958_zero, Shared.RelationChunk021.relation959_zero, Shared.RelationChunk021.relation960_zero, Shared.RelationChunk021.relation961_zero, Shared.RelationChunk021.relation962_zero, Shared.RelationChunk021.relation963_zero, Shared.RelationChunk021.relation964_zero, Shared.RelationChunk021.relation965_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8578 128 := by cbv
private def targetRows : List BasisRow := [⟨28, 163, 1, "0,2,8,2,291,1"⟩,
  ⟨27, 163, 0, "0,2,8,2,292,1"⟩,
  ⟨27, 163, 1, "0,3,642,1"⟩,
  ⟨26, 163, 0, "0,2,654,1"⟩,
  ⟨25, 163, 0, "0,5,627,1"⟩,
  ⟨24, 163, 0, "0,3,645,1"⟩,
  ⟨24, 163, 1, "0,3,644,1"⟩,
  ⟨23, 163, 0, "0,3,646,1"⟩,
  ⟨22, 163, 0, "13,4,75,1"⟩,
  ⟨22, 163, 1, "0,1,666,1"⟩,
  ⟨22, 163, 2, "0,2,655,1"⟩,
  ⟨21, 163, 0, "13,4,76,1"⟩,
  ⟨21, 163, 1, "1,1,655,1"⟩,
  ⟨21, 163, 2, "0,1,667,1"⟩,
  ⟨18, 163, 0, "8,2,312,1"⟩,
  ⟨18, 163, 1, "0,1,8,1,502,1"⟩,
  ⟨17, 163, 0, "8,2,314,1"⟩,
  ⟨17, 163, 2, "0,1,16,1,367,1"⟩,
  ⟨16, 163, 0, "677,1"⟩,
  ⟨16, 163, 1, "8,1,511,1"⟩,
  ⟨16, 163, 2, "0,1,669,1"⟩,
  ⟨16, 163, 3, "0,1,17,1,367,1"⟩,
  ⟨15, 163, 0, "679,1"⟩,
  ⟨15, 163, 1, "678,1"⟩,
  ⟨15, 163, 2, "67,1,174,1"⟩,
  ⟨15, 163, 3, "0,1,671,1"⟩,
  ⟨15, 163, 4, "0,3,652,1"⟩,
  ⟨14, 163, 1, "68,1,174,1"⟩,
  ⟨14, 163, 2, "13,1,450,1"⟩,
  ⟨14, 163, 3, "1,1,657,1"⟩,
  ⟨14, 163, 4, "0,4,18,1,314,1"⟩,
  ⟨13, 163, 1, "682,1"⟩,
  ⟨13, 163, 2, "681,1"⟩,
  ⟨13, 163, 3, "0,1,673,1"⟩,
  ⟨13, 163, 4, "0,5,17,1,324,1"⟩,
  ⟨12, 163, 1, "0,1,674,1"⟩,
  ⟨12, 163, 2, "0,2,19,1,69,2"⟩,
  ⟨12, 163, 3, "0,2,18,1,333,1"⟩,
  ⟨11, 163, 0, "0,2,659,1"⟩,
  ⟨11, 163, 1, "0,2,20,1,69,2"⟩,
  ⟨11, 163, 2, "0,2,19,1,324,1"⟩,
  ⟨10, 163, 0, "7,2,352,1"⟩,
  ⟨10, 163, 1, "0,2,20,1,324,1"⟩,
  ⟨9, 163, 0, "18,1,352,1"⟩,
  ⟨9, 163, 1, "1,1,70,1,163,1"⟩,
  ⟨9, 163, 2, "0,1,676,1"⟩,
  ⟨8, 163, 1, "0,3,7,1,508,1"⟩,
  ⟨7, 163, 0, "0,2,660,1"⟩,
  ⟨6, 163, 1, "0,3,7,2,324,1"⟩,
  ⟨5, 163, 0, "0,3,18,1,324,1"⟩,
  ⟨164, 164, 0, "0,164"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5150_mem, Shared.BasisChunk005.row5151_mem, Shared.BasisChunk005.row5152_mem, Shared.BasisChunk005.row5153_mem, Shared.BasisChunk005.row5154_mem, Shared.BasisChunk005.row5155_mem, Shared.BasisChunk005.row5156_mem, Shared.BasisChunk005.row5157_mem, Shared.BasisChunk005.row5158_mem, Shared.BasisChunk005.row5159_mem, Shared.BasisChunk005.row5160_mem, Shared.BasisChunk005.row5161_mem, Shared.BasisChunk005.row5162_mem, Shared.BasisChunk005.row5163_mem, Shared.BasisChunk005.row5164_mem, Shared.BasisChunk005.row5165_mem, Shared.BasisChunk005.row5166_mem, Shared.BasisChunk005.row5168_mem, Shared.BasisChunk005.row5169_mem, Shared.BasisChunk005.row5170_mem, Shared.BasisChunk005.row5171_mem, Shared.BasisChunk005.row5172_mem, Shared.BasisChunk005.row5173_mem, Shared.BasisChunk005.row5174_mem, Shared.BasisChunk005.row5175_mem, Shared.BasisChunk005.row5176_mem, Shared.BasisChunk005.row5177_mem, Shared.BasisChunk005.row5179_mem, Shared.BasisChunk005.row5180_mem, Shared.BasisChunk005.row5181_mem, Shared.BasisChunk005.row5182_mem, Shared.BasisChunk005.row5184_mem, Shared.BasisChunk005.row5185_mem, Shared.BasisChunk005.row5186_mem, Shared.BasisChunk005.row5187_mem, Shared.BasisChunk005.row5189_mem, Shared.BasisChunk005.row5190_mem, Shared.BasisChunk005.row5191_mem, Shared.BasisChunk005.row5192_mem, Shared.BasisChunk005.row5193_mem, Shared.BasisChunk005.row5194_mem, Shared.BasisChunk005.row5195_mem, Shared.BasisChunk005.row5196_mem, Shared.BasisChunk005.row5197_mem, Shared.BasisChunk005.row5198_mem, Shared.BasisChunk005.row5199_mem, Shared.BasisChunk005.row5201_mem, Shared.BasisChunk005.row5202_mem, Shared.BasisChunk005.row5204_mem, Shared.BasisChunk005.row5205_mem, Shared.BasisChunk005.row5206_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard067
