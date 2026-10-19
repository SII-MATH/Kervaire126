module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard077
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk027
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard077
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard077
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk009.relation496_zero, Shared.RelationChunk009.relation497_zero, Shared.RelationChunk009.relation498_zero, Shared.RelationChunk013.relation664_zero, Shared.RelationChunk013.relation665_zero, Shared.RelationChunk013.relation666_zero, Shared.RelationChunk013.relation667_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk015.relation769_zero, Shared.RelationChunk015.relation770_zero, Shared.RelationChunk015.relation772_zero, Shared.RelationChunk015.relation773_zero, Shared.RelationChunk015.relation774_zero, Shared.RelationChunk015.relation775_zero, Shared.RelationChunk015.relation776_zero, Shared.RelationChunk015.relation778_zero, Shared.RelationChunk016.relation798_zero, Shared.RelationChunk016.relation799_zero, Shared.RelationChunk016.relation800_zero, Shared.RelationChunk025.relation1110_zero, Shared.RelationChunk026.relation1112_zero, Shared.RelationChunk026.relation1113_zero, Shared.RelationChunk026.relation1114_zero, Shared.RelationChunk026.relation1115_zero, Shared.RelationChunk026.relation1116_zero, Shared.RelationChunk026.relation1120_zero, Shared.RelationChunk026.relation1122_zero, Shared.RelationChunk026.relation1123_zero, Shared.RelationChunk027.relation1153_zero, Shared.RelationChunk027.relation1154_zero, Shared.RelationChunk027.relation1155_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9858 128 := by cbv
private def targetRows : List BasisRow := [⟨27, 170, 1, "13,3,167,1"⟩,
  ⟨27, 170, 2, "8,1,574,1"⟩,
  ⟨27, 170, 3, "0,1,753,1"⟩,
  ⟨27, 170, 4, "0,5,64,1,187,1"⟩,
  ⟨26, 170, 0, "13,3,168,1"⟩,
  ⟨26, 170, 1, "8,1,9,1,346,1"⟩,
  ⟨26, 170, 2, "8,2,382,1"⟩,
  ⟨26, 170, 3, "0,5,64,1,188,1"⟩,
  ⟨25, 170, 0, "9,1,13,1,292,1"⟩,
  ⟨25, 170, 1, "8,2,383,1"⟩,
  ⟨24, 170, 0, "8,3,250,1"⟩,
  ⟨24, 170, 1, "0,4,717,1"⟩,
  ⟨24, 170, 2, "0,5,706,1"⟩,
  ⟨23, 170, 0, "8,2,384,1"⟩,
  ⟨23, 170, 1, "0,1,8,1,69,1,138,1"⟩,
  ⟨23, 170, 2, "0,2,3,1,646,1"⟩,
  ⟨23, 170, 3, "0,6,693,1"⟩,
  ⟨22, 170, 0, "8,1,9,1,13,1,209,1"⟩,
  ⟨22, 170, 1, "0,2,739,1"⟩,
  ⟨21, 170, 0, "9,1,13,1,294,1"⟩,
  ⟨21, 170, 1, "0,2,43,1,266,1"⟩,
  ⟨20, 170, 1, "0,2,43,1,267,1"⟩,
  ⟨17, 170, 1, "0,2,741,1"⟩,
  ⟨16, 170, 1, "3,1,669,1"⟩,
  ⟨16, 170, 2, "0,2,30,1,324,1"⟩,
  ⟨16, 170, 3, "0,8,676,1"⟩,
  ⟨15, 170, 0, "765,1"⟩,
  ⟨15, 170, 2, "0,3,732,1"⟩,
  ⟨14, 170, 0, "767,1"⟩,
  ⟨14, 170, 2, "67,1,203,1"⟩,
  ⟨13, 170, 0, "768,1"⟩,
  ⟨13, 170, 1, "68,1,203,1"⟩,
  ⟨13, 170, 3, "3,1,673,1"⟩,
  ⟨13, 170, 4, "1,2,719,1"⟩,
  ⟨13, 170, 5, "0,2,743,1"⟩,
  ⟨12, 170, 0, "769,1"⟩,
  ⟨12, 170, 1, "3,1,674,1"⟩,
  ⟨12, 170, 2, "2,1,719,1"⟩,
  ⟨12, 170, 3, "1,1,744,1"⟩,
  ⟨12, 170, 4, "0,1,755,1"⟩,
  ⟨12, 170, 5, "0,10,18,1,324,1"⟩,
  ⟨11, 170, 0, "770,1"⟩,
  ⟨11, 170, 1, "0,1,757,1"⟩,
  ⟨11, 170, 2, "0,1,756,1"⟩,
  ⟨11, 170, 3, "0,1,3,1,659,1"⟩,
  ⟨10, 170, 0, "773,1"⟩,
  ⟨10, 170, 1, "772,1"⟩,
  ⟨10, 170, 2, "771,1"⟩,
  ⟨9, 170, 0, "775,1"⟩,
  ⟨9, 170, 1, "774,1"⟩,
  ⟨9, 170, 2, "18,1,445,1"⟩,
  ⟨9, 170, 4, "0,2,747,1"⟩,
  ⟨8, 170, 0, "776,1"⟩,
  ⟨8, 170, 1, "32,1,324,1"⟩,
  ⟨8, 170, 2, "1,1,748,1"⟩,
  ⟨8, 170, 3, "1,1,747,1"⟩,
  ⟨8, 170, 4, "0,2,749,1"⟩,
  ⟨7, 170, 3, "0,2,750,1"⟩,
  ⟨6, 170, 1, "1,1,750,1"⟩,
  ⟨6, 170, 2, "0,2,751,1"⟩,
  ⟨5, 170, 2, "0,2,3,1,18,1,324,1"⟩,
  ⟨171, 171, 0, "0,171"⟩,
  ⟨51, 171, 0, "8,1,579,1"⟩,
  ⟨50, 171, 0, "17,1,470,1"⟩,
  ⟨49, 171, 0, "777,1"⟩,
  ⟨48, 171, 0, "8,3,252,1"⟩,
  ⟨47, 171, 0, "8,3,253,1"⟩,
  ⟨46, 171, 0, "8,2,17,1,200,1"⟩,
  ⟨45, 171, 0, "8,2,401,1"⟩,
  ⟨45, 171, 1, "0,7,686,1"⟩,
  ⟨44, 171, 0, "8,5,116,1"⟩,
  ⟨44, 171, 1, "0,43,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5892_mem, Shared.BasisChunk005.row5893_mem, Shared.BasisChunk005.row5894_mem, Shared.BasisChunk005.row5895_mem, Shared.BasisChunk005.row5896_mem, Shared.BasisChunk005.row5897_mem, Shared.BasisChunk005.row5898_mem, Shared.BasisChunk005.row5899_mem, Shared.BasisChunk005.row5900_mem, Shared.BasisChunk005.row5901_mem, Shared.BasisChunk005.row5902_mem, Shared.BasisChunk005.row5903_mem, Shared.BasisChunk005.row5904_mem, Shared.BasisChunk005.row5905_mem, Shared.BasisChunk005.row5906_mem, Shared.BasisChunk005.row5907_mem, Shared.BasisChunk005.row5908_mem, Shared.BasisChunk005.row5909_mem, Shared.BasisChunk005.row5910_mem, Shared.BasisChunk005.row5911_mem, Shared.BasisChunk005.row5912_mem, Shared.BasisChunk005.row5914_mem, Shared.BasisChunk005.row5918_mem, Shared.BasisChunk005.row5920_mem, Shared.BasisChunk005.row5921_mem, Shared.BasisChunk005.row5922_mem, Shared.BasisChunk005.row5923_mem, Shared.BasisChunk005.row5925_mem, Shared.BasisChunk005.row5926_mem, Shared.BasisChunk005.row5928_mem, Shared.BasisChunk005.row5929_mem, Shared.BasisChunk005.row5930_mem, Shared.BasisChunk005.row5932_mem, Shared.BasisChunk005.row5933_mem, Shared.BasisChunk005.row5934_mem, Shared.BasisChunk005.row5935_mem, Shared.BasisChunk005.row5936_mem, Shared.BasisChunk005.row5937_mem, Shared.BasisChunk005.row5938_mem, Shared.BasisChunk005.row5939_mem, Shared.BasisChunk005.row5940_mem, Shared.BasisChunk005.row5941_mem, Shared.BasisChunk005.row5942_mem, Shared.BasisChunk005.row5943_mem, Shared.BasisChunk005.row5944_mem, Shared.BasisChunk005.row5945_mem, Shared.BasisChunk005.row5946_mem, Shared.BasisChunk005.row5947_mem, Shared.BasisChunk005.row5949_mem, Shared.BasisChunk005.row5950_mem, Shared.BasisChunk005.row5951_mem, Shared.BasisChunk005.row5953_mem, Shared.BasisChunk005.row5954_mem, Shared.BasisChunk005.row5955_mem, Shared.BasisChunk005.row5956_mem, Shared.BasisChunk005.row5957_mem, Shared.BasisChunk005.row5958_mem, Shared.BasisChunk005.row5962_mem, Shared.BasisChunk005.row5964_mem, Shared.BasisChunk005.row5965_mem, Shared.BasisChunk005.row5968_mem, Shared.BasisChunk005.row5970_mem, Shared.BasisChunk005.row5972_mem, Shared.BasisChunk005.row5973_mem, Shared.BasisChunk005.row5974_mem, Shared.BasisChunk005.row5975_mem, Shared.BasisChunk005.row5976_mem, Shared.BasisChunk005.row5977_mem, Shared.BasisChunk005.row5978_mem, Shared.BasisChunk005.row5979_mem, Shared.BasisChunk005.row5980_mem, Shared.BasisChunk005.row5981_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard077
