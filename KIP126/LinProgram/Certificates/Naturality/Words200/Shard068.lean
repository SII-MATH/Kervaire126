module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard068
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard068
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard068
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation47_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk002.relation217_zero, Shared.RelationChunk005.relation357_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk007.relation417_zero, Shared.RelationChunk007.relation441_zero, Shared.RelationChunk008.relation481_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation553_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk011.relation602_zero, Shared.RelationChunk012.relation660_zero, Shared.RelationChunk012.relation661_zero, Shared.RelationChunk012.relation662_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk013.relation672_zero, Shared.RelationChunk013.relation673_zero, Shared.RelationChunk013.relation675_zero, Shared.RelationChunk021.relation967_zero, Shared.RelationChunk022.relation968_zero, Shared.RelationChunk022.relation969_zero, Shared.RelationChunk022.relation970_zero, Shared.RelationChunk022.relation972_zero, Shared.RelationChunk022.relation973_zero, Shared.RelationChunk022.relation974_zero, Shared.RelationChunk022.relation975_zero, Shared.RelationChunk022.relation976_zero, Shared.RelationChunk022.relation977_zero, Shared.RelationChunk022.relation979_zero, Shared.RelationChunk022.relation980_zero, Shared.RelationChunk022.relation981_zero, Shared.RelationChunk022.relation982_zero, Shared.RelationChunk022.relation983_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8706 128 := by cbv
private def targetRows : List BasisRow := [⟨54, 164, 0, "0,2,661,1"⟩,
  ⟨53, 164, 1, "0,8,606,1"⟩,
  ⟨50, 164, 0, "0,2,8,2,295,1"⟩,
  ⟨49, 164, 0, "0,2,8,2,296,1"⟩,
  ⟨47, 164, 0, "0,5,635,1"⟩,
  ⟨46, 164, 0, "0,5,636,1"⟩,
  ⟨44, 164, 0, "0,2,662,1"⟩,
  ⟨43, 164, 0, "0,2,663,1"⟩,
  ⟨39, 164, 0, "0,2,8,2,298,1"⟩,
  ⟨37, 164, 1, "0,36,324,1"⟩,
  ⟨36, 164, 0, "8,1,16,1,244,1"⟩,
  ⟨35, 164, 0, "8,1,17,1,244,1"⟩,
  ⟨34, 164, 0, "8,1,16,1,245,1"⟩,
  ⟨33, 164, 0, "8,2,315,1"⟩,
  ⟨32, 164, 0, "8,4,149,1"⟩,
  ⟨31, 164, 0, "8,2,16,1,167,1"⟩,
  ⟨30, 164, 1, "8,3,218,1"⟩,
  ⟨29, 164, 0, "17,1,380,1"⟩,
  ⟨29, 164, 1, "8,3,219,1"⟩,
  ⟨28, 164, 1, "8,2,13,1,194,1"⟩,
  ⟨28, 164, 2, "0,4,642,1"⟩,
  ⟨27, 164, 0, "689,1"⟩,
  ⟨27, 164, 1, "8,1,13,2,167,1"⟩,
  ⟨27, 164, 2, "0,3,654,1"⟩,
  ⟨26, 164, 0, "13,2,248,1"⟩,
  ⟨26, 164, 1, "8,1,517,1"⟩,
  ⟨26, 164, 4, "0,6,627,1"⟩,
  ⟨25, 164, 0, "13,3,150,1"⟩,
  ⟨25, 164, 1, "8,1,518,1"⟩,
  ⟨25, 164, 2, "8,1,9,1,292,1"⟩,
  ⟨25, 164, 3, "0,4,645,1"⟩,
  ⟨25, 164, 4, "0,4,644,1"⟩,
  ⟨24, 164, 0, "23,1,316,1"⟩,
  ⟨24, 164, 1, "8,2,318,1"⟩,
  ⟨24, 164, 2, "0,4,646,1"⟩,
  ⟨23, 164, 0, "8,1,9,1,293,1"⟩,
  ⟨23, 164, 1, "0,2,666,1"⟩,
  ⟨23, 164, 2, "0,3,655,1"⟩,
  ⟨22, 164, 0, "8,2,9,1,209,1"⟩,
  ⟨21, 164, 0, "8,1,9,1,294,1"⟩,
  ⟨21, 164, 1, "2,1,646,1"⟩,
  ⟨20, 164, 1, "9,1,13,1,261,1"⟩,
  ⟨20, 164, 2, "3,1,609,1"⟩,
  ⟨19, 164, 0, "0,1,8,2,312,1"⟩,
  ⟨19, 164, 1, "0,2,8,1,502,1"⟩,
  ⟨18, 164, 0, "0,1,3,1,604,1"⟩,
  ⟨18, 164, 1, "0,2,16,1,367,1"⟩,
  ⟨17, 164, 3, "0,2,669,1"⟩,
  ⟨17, 164, 4, "0,2,17,1,367,1"⟩,
  ⟨16, 164, 1, "0,1,678,1"⟩,
  ⟨16, 164, 2, "0,1,67,1,174,1"⟩,
  ⟨16, 164, 3, "0,2,671,1"⟩,
  ⟨14, 164, 0, "0,2,673,1"⟩,
  ⟨13, 164, 0, "2,1,652,1"⟩,
  ⟨13, 164, 1, "1,1,673,1"⟩,
  ⟨13, 164, 2, "0,3,18,1,333,1"⟩,
  ⟨12, 164, 0, "3,2,544,1"⟩,
  ⟨12, 164, 1, "1,1,674,1"⟩,
  ⟨12, 164, 2, "0,3,19,1,324,1"⟩,
  ⟨11, 164, 0, "0,1,7,2,352,1"⟩,
  ⟨10, 164, 1, "0,1,18,1,352,1"⟩,
  ⟨10, 164, 2, "0,2,676,1"⟩,
  ⟨9, 164, 0, "18,1,367,1"⟩,
  ⟨9, 164, 3, "1,1,676,1"⟩,
  ⟨9, 164, 4, "0,1,684,1"⟩,
  ⟨8, 164, 1, "696,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5207_mem, Shared.BasisChunk005.row5209_mem, Shared.BasisChunk005.row5210_mem, Shared.BasisChunk005.row5211_mem, Shared.BasisChunk005.row5212_mem, Shared.BasisChunk005.row5213_mem, Shared.BasisChunk005.row5214_mem, Shared.BasisChunk005.row5215_mem, Shared.BasisChunk005.row5217_mem, Shared.BasisChunk005.row5220_mem, Shared.BasisChunk005.row5221_mem, Shared.BasisChunk005.row5222_mem, Shared.BasisChunk005.row5223_mem, Shared.BasisChunk005.row5224_mem, Shared.BasisChunk005.row5226_mem, Shared.BasisChunk005.row5227_mem, Shared.BasisChunk005.row5229_mem, Shared.BasisChunk005.row5231_mem, Shared.BasisChunk005.row5232_mem, Shared.BasisChunk005.row5234_mem, Shared.BasisChunk005.row5235_mem, Shared.BasisChunk005.row5236_mem, Shared.BasisChunk005.row5237_mem, Shared.BasisChunk005.row5238_mem, Shared.BasisChunk005.row5239_mem, Shared.BasisChunk005.row5240_mem, Shared.BasisChunk005.row5243_mem, Shared.BasisChunk005.row5244_mem, Shared.BasisChunk005.row5245_mem, Shared.BasisChunk005.row5246_mem, Shared.BasisChunk005.row5247_mem, Shared.BasisChunk005.row5248_mem, Shared.BasisChunk005.row5249_mem, Shared.BasisChunk005.row5250_mem, Shared.BasisChunk005.row5251_mem, Shared.BasisChunk005.row5252_mem, Shared.BasisChunk005.row5253_mem, Shared.BasisChunk005.row5254_mem, Shared.BasisChunk005.row5255_mem, Shared.BasisChunk005.row5257_mem, Shared.BasisChunk005.row5258_mem, Shared.BasisChunk005.row5260_mem, Shared.BasisChunk005.row5261_mem, Shared.BasisChunk005.row5262_mem, Shared.BasisChunk005.row5263_mem, Shared.BasisChunk005.row5264_mem, Shared.BasisChunk005.row5265_mem, Shared.BasisChunk005.row5269_mem, Shared.BasisChunk005.row5270_mem, Shared.BasisChunk005.row5272_mem, Shared.BasisChunk005.row5273_mem, Shared.BasisChunk005.row5274_mem, Shared.BasisChunk005.row5277_mem, Shared.BasisChunk005.row5278_mem, Shared.BasisChunk005.row5279_mem, Shared.BasisChunk005.row5280_mem, Shared.BasisChunk005.row5281_mem, Shared.BasisChunk005.row5282_mem, Shared.BasisChunk005.row5283_mem, Shared.BasisChunk005.row5284_mem, Shared.BasisChunk005.row5286_mem, Shared.BasisChunk005.row5287_mem, Shared.BasisChunk005.row5288_mem, Shared.BasisChunk005.row5291_mem, Shared.BasisChunk005.row5292_mem, Shared.BasisChunk005.row5294_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard068
