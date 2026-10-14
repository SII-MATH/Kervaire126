module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard074
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard074
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard074
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
  exact ⟨Shared.RelationChunk000.relation38_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk007.relation420_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk012.relation626_zero, Shared.RelationChunk014.relation732_zero, Shared.RelationChunk014.relation737_zero, Shared.RelationChunk014.relation738_zero, Shared.RelationChunk024.relation1052_zero, Shared.RelationChunk024.relation1053_zero, Shared.RelationChunk024.relation1054_zero, Shared.RelationChunk024.relation1055_zero, Shared.RelationChunk024.relation1056_zero, Shared.RelationChunk024.relation1057_zero, Shared.RelationChunk024.relation1058_zero, Shared.RelationChunk024.relation1059_zero, Shared.RelationChunk024.relation1060_zero, Shared.RelationChunk024.relation1061_zero, Shared.RelationChunk024.relation1062_zero, Shared.RelationChunk024.relation1063_zero, Shared.RelationChunk024.relation1064_zero, Shared.RelationChunk024.relation1065_zero, Shared.RelationChunk024.relation1066_zero, Shared.RelationChunk024.relation1067_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9474 128 := by cbv
private def targetRows : List BasisRow := [⟨27, 168, 0, "13,4,23,1,24,1"⟩,
  ⟨27, 168, 1, "8,1,9,1,13,1,23,1,80,1"⟩,
  ⟨27, 168, 2, "8,2,16,1,188,1"⟩,
  ⟨26, 168, 0, "9,1,13,3,101,1"⟩,
  ⟨26, 168, 1, "8,2,17,1,188,1"⟩,
  ⟨25, 168, 0, "8,1,17,1,267,1"⟩,
  ⟨25, 168, 1, "0,3,64,1,187,1"⟩,
  ⟨24, 168, 0, "8,2,13,1,212,1"⟩,
  ⟨24, 168, 1, "0,3,702,1"⟩,
  ⟨24, 168, 2, "0,3,64,1,188,1"⟩,
  ⟨23, 168, 0, "13,2,266,1"⟩,
  ⟨23, 168, 1, "8,1,13,2,188,1"⟩,
  ⟨23, 168, 2, "0,3,703,1"⟩,
  ⟨22, 168, 0, "737,1"⟩,
  ⟨22, 168, 2, "13,2,267,1"⟩,
  ⟨22, 168, 3, "9,1,13,1,286,1"⟩,
  ⟨22, 168, 4, "0,2,717,1"⟩,
  ⟨22, 168, 5, "0,3,706,1"⟩,
  ⟨21, 168, 0, "72,1,188,1"⟩,
  ⟨21, 168, 1, "13,2,268,1"⟩,
  ⟨21, 168, 3, "2,1,690,1"⟩,
  ⟨21, 168, 4, "0,2,3,1,628,1"⟩,
  ⟨21, 168, 5, "0,4,693,1"⟩,
  ⟨20, 168, 0, "739,1"⟩,
  ⟨20, 168, 1, "738,1"⟩,
  ⟨19, 168, 1, "13,1,23,1,213,1"⟩,
  ⟨19, 168, 2, "0,1,729,1"⟩,
  ⟨19, 168, 3, "0,3,707,1"⟩,
  ⟨18, 168, 0, "43,1,267,1"⟩,
  ⟨18, 168, 1, "9,1,13,1,288,1"⟩,
  ⟨18, 168, 2, "1,1,3,1,629,1"⟩,
  ⟨17, 168, 0, "3,1,648,1"⟩,
  ⟨17, 168, 1, "0,2,67,1,190,1"⟩,
  ⟨16, 168, 0, "8,2,367,1"⟩,
  ⟨16, 168, 1, "3,1,650,1"⟩,
  ⟨15, 168, 0, "741,1"⟩,
  ⟨15, 168, 1, "740,1"⟩,
  ⟨15, 168, 2, "67,1,197,1"⟩,
  ⟨15, 168, 3, "8,1,562,1"⟩,
  ⟨14, 168, 0, "742,1"⟩,
  ⟨14, 168, 1, "30,1,324,1"⟩,
  ⟨14, 168, 2, "8,1,563,1"⟩,
  ⟨14, 168, 3, "0,1,731,1"⟩,
  ⟨14, 168, 4, "0,1,730,1"⟩,
  ⟨14, 168, 5, "0,6,676,1"⟩,
  ⟨13, 168, 0, "3,1,652,1"⟩,
  ⟨13, 168, 1, "0,1,733,1"⟩,
  ⟨13, 168, 2, "0,1,732,1"⟩,
  ⟨13, 168, 3, "0,2,719,1"⟩,
  ⟨12, 168, 0, "23,1,368,1"⟩,
  ⟨12, 168, 2, "0,1,734,1"⟩,
  ⟨12, 168, 3, "0,4,696,1"⟩,
  ⟨11, 168, 0, "745,1"⟩,
  ⟨11, 168, 1, "744,1"⟩,
  ⟨11, 168, 2, "743,1"⟩,
  ⟨11, 168, 3, "18,1,419,1"⟩,
  ⟨11, 168, 4, "0,1,18,1,414,1"⟩,
  ⟨11, 168, 5, "0,4,23,1,324,1"⟩,
  ⟨10, 168, 0, "746,1"⟩,
  ⟨10, 168, 1, "0,1,18,1,415,1"⟩,
  ⟨10, 168, 2, "0,1,8,1,9,1,324,1"⟩,
  ⟨10, 168, 3, "0,2,720,1"⟩,
  ⟨10, 168, 4, "0,8,18,1,324,1"⟩,
  ⟨9, 168, 0, "2,1,697,1"⟩,
  ⟨9, 168, 1, "1,1,720,1"⟩,
  ⟨9, 168, 2, "0,1,29,1,324,1"⟩,
  ⟨8, 168, 0, "2,1,698,1"⟩,
  ⟨8, 168, 1, "2,1,24,1,69,2"⟩,
  ⟨8, 168, 2, "2,1,18,1,368,1"⟩,
  ⟨8, 168, 3, "1,1,28,1,324,1"⟩,
  ⟨7, 168, 2, "2,1,699,1"⟩,
  ⟨7, 168, 3, "2,1,24,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5679_mem, Shared.BasisChunk005.row5680_mem, Shared.BasisChunk005.row5681_mem, Shared.BasisChunk005.row5682_mem, Shared.BasisChunk005.row5683_mem, Shared.BasisChunk005.row5685_mem, Shared.BasisChunk005.row5686_mem, Shared.BasisChunk005.row5687_mem, Shared.BasisChunk005.row5688_mem, Shared.BasisChunk005.row5689_mem, Shared.BasisChunk005.row5690_mem, Shared.BasisChunk005.row5691_mem, Shared.BasisChunk005.row5692_mem, Shared.BasisChunk005.row5693_mem, Shared.BasisChunk005.row5695_mem, Shared.BasisChunk005.row5696_mem, Shared.BasisChunk005.row5697_mem, Shared.BasisChunk005.row5698_mem, Shared.BasisChunk005.row5699_mem, Shared.BasisChunk005.row5700_mem, Shared.BasisChunk005.row5702_mem, Shared.BasisChunk005.row5703_mem, Shared.BasisChunk005.row5704_mem, Shared.BasisChunk005.row5705_mem, Shared.BasisChunk005.row5706_mem, Shared.BasisChunk005.row5709_mem, Shared.BasisChunk005.row5710_mem, Shared.BasisChunk005.row5711_mem, Shared.BasisChunk005.row5712_mem, Shared.BasisChunk005.row5713_mem, Shared.BasisChunk005.row5714_mem, Shared.BasisChunk005.row5715_mem, Shared.BasisChunk005.row5716_mem, Shared.BasisChunk005.row5717_mem, Shared.BasisChunk005.row5718_mem, Shared.BasisChunk005.row5720_mem, Shared.BasisChunk005.row5721_mem, Shared.BasisChunk005.row5722_mem, Shared.BasisChunk005.row5723_mem, Shared.BasisChunk005.row5725_mem, Shared.BasisChunk005.row5726_mem, Shared.BasisChunk005.row5727_mem, Shared.BasisChunk005.row5728_mem, Shared.BasisChunk005.row5729_mem, Shared.BasisChunk005.row5730_mem, Shared.BasisChunk005.row5731_mem, Shared.BasisChunk005.row5732_mem, Shared.BasisChunk005.row5733_mem, Shared.BasisChunk005.row5734_mem, Shared.BasisChunk005.row5735_mem, Shared.BasisChunk005.row5737_mem, Shared.BasisChunk005.row5738_mem, Shared.BasisChunk005.row5739_mem, Shared.BasisChunk005.row5740_mem, Shared.BasisChunk005.row5741_mem, Shared.BasisChunk005.row5742_mem, Shared.BasisChunk005.row5743_mem, Shared.BasisChunk005.row5744_mem, Shared.BasisChunk005.row5745_mem, Shared.BasisChunk005.row5746_mem, Shared.BasisChunk005.row5747_mem, Shared.BasisChunk005.row5748_mem, Shared.BasisChunk005.row5749_mem, Shared.BasisChunk005.row5750_mem, Shared.BasisChunk005.row5751_mem, Shared.BasisChunk005.row5752_mem, Shared.BasisChunk005.row5753_mem, Shared.BasisChunk005.row5754_mem, Shared.BasisChunk005.row5755_mem, Shared.BasisChunk005.row5756_mem, Shared.BasisChunk005.row5759_mem, Shared.BasisChunk005.row5760_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard074
