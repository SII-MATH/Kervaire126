module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard073
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard073
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard073
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation26_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation63_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk001.relation156_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation232_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation306_zero, Shared.RelationChunk004.relation307_zero, Shared.RelationChunk004.relation308_zero, Shared.RelationChunk004.relation315_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk008.relation452_zero, Shared.RelationChunk008.relation453_zero, Shared.RelationChunk008.relation455_zero, Shared.RelationChunk008.relation457_zero, Shared.RelationChunk008.relation458_zero, Shared.RelationChunk008.relation482_zero, Shared.RelationChunk008.relation483_zero, Shared.RelationChunk010.relation537_zero, Shared.RelationChunk014.relation725_zero, Shared.RelationChunk014.relation739_zero, Shared.RelationChunk014.relation740_zero, Shared.RelationChunk014.relation741_zero, Shared.RelationChunk014.relation742_zero, Shared.RelationChunk014.relation743_zero, Shared.RelationChunk014.relation745_zero, Shared.RelationChunk014.relation750_zero, Shared.RelationChunk023.relation1014_zero, Shared.RelationChunk023.relation1035_zero, Shared.RelationChunk023.relation1036_zero, Shared.RelationChunk025.relation1068_zero, Shared.RelationChunk025.relation1069_zero, Shared.RelationChunk025.relation1070_zero, Shared.RelationChunk025.relation1072_zero, Shared.RelationChunk025.relation1073_zero, Shared.RelationChunk025.relation1074_zero, Shared.RelationChunk025.relation1075_zero, Shared.RelationChunk025.relation1076_zero, Shared.RelationChunk025.relation1077_zero, Shared.RelationChunk025.relation1079_zero, Shared.RelationChunk025.relation1080_zero, Shared.RelationChunk025.relation1081_zero, Shared.RelationChunk025.relation1082_zero, Shared.RelationChunk025.relation1083_zero, Shared.RelationChunk025.relation1084_zero, Shared.RelationChunk025.relation1085_zero, Shared.RelationChunk025.relation1086_zero, Shared.RelationChunk025.relation1087_zero, Shared.RelationChunk025.relation1088_zero, Shared.RelationChunk025.relation1089_zero, Shared.RelationChunk025.relation1090_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9346 128 := by cbv
private def targetRows : List BasisRow := [⟨13, 167, 0, "731,1"⟩,
  ⟨13, 167, 2, "18,1,408,1"⟩,
  ⟨13, 167, 3, "0,5,676,1"⟩,
  ⟨12, 167, 0, "733,1"⟩,
  ⟨12, 167, 2, "18,1,411,1"⟩,
  ⟨12, 167, 3, "1,1,712,1"⟩,
  ⟨12, 167, 4, "0,1,719,1"⟩,
  ⟨12, 167, 5, "0,3,7,1,546,1"⟩,
  ⟨11, 167, 0, "735,1"⟩,
  ⟨11, 167, 3, "0,3,696,1"⟩,
  ⟨10, 167, 1, "1,1,18,1,376,1"⟩,
  ⟨10, 167, 3, "0,1,2,1,676,1"⟩,
  ⟨10, 167, 4, "0,3,23,1,324,1"⟩,
  ⟨9, 167, 0, "18,1,415,1"⟩,
  ⟨9, 167, 2, "0,1,720,1"⟩,
  ⟨9, 167, 3, "0,1,7,2,398,1"⟩,
  ⟨9, 167, 4, "0,7,18,1,324,1"⟩,
  ⟨8, 167, 0, "29,1,324,1"⟩,
  ⟨8, 167, 1, "0,2,2,1,660,1"⟩,
  ⟨168, 168, 0, "0,168"⟩,
  ⟨55, 168, 0, "0,3,700,1"⟩,
  ⟨51, 168, 0, "8,1,554,1"⟩,
  ⟨48, 168, 0, "8,3,236,1"⟩,
  ⟨47, 168, 0, "8,2,16,1,183,1"⟩,
  ⟨46, 168, 0, "8,2,17,1,183,1"⟩,
  ⟨45, 168, 0, "8,2,354,1"⟩,
  ⟨44, 168, 0, "8,5,110,1"⟩,
  ⟨44, 168, 1, "0,4,685,1"⟩,
  ⟨43, 168, 0, "8,5,111,1"⟩,
  ⟨43, 168, 1, "0,3,17,1,403,1"⟩,
  ⟨42, 168, 1, "8,3,16,1,17,1,50,1"⟩,
  ⟨42, 168, 3, "0,4,686,1"⟩,
  ⟨41, 168, 0, "8,1,556,1"⟩,
  ⟨41, 168, 1, "8,4,161,1"⟩,
  ⟨41, 168, 2, "0,1,722,1"⟩,
  ⟨41, 168, 3, "0,40,324,1"⟩,
  ⟨40, 168, 0, "17,1,433,1"⟩,
  ⟨40, 168, 1, "8,7,31,1"⟩,
  ⟨39, 168, 0, "8,6,16,1,17,1"⟩,
  ⟨39, 168, 1, "0,1,723,1"⟩,
  ⟨38, 168, 0, "8,3,237,1"⟩,
  ⟨38, 168, 1, "8,6,17,2"⟩,
  ⟨37, 168, 0, "8,3,238,1"⟩,
  ⟨37, 168, 1, "8,6,60,1"⟩,
  ⟨36, 168, 0, "8,2,17,1,185,1"⟩,
  ⟨36, 168, 1, "8,8,13,1"⟩,
  ⟨35, 168, 0, "8,1,17,2,147,1"⟩,
  ⟨35, 168, 1, "8,7,32,1"⟩,
  ⟨35, 168, 2, "0,1,725,1"⟩,
  ⟨34, 168, 0, "8,5,112,1"⟩,
  ⟨34, 168, 1, "8,6,13,1,23,1"⟩,
  ⟨33, 168, 0, "8,5,113,1"⟩,
  ⟨33, 168, 1, "8,5,13,1,51,1"⟩,
  ⟨32, 168, 1, "8,4,162,1"⟩,
  ⟨32, 168, 2, "8,4,13,4"⟩,
  ⟨31, 168, 0, "8,1,64,1,138,1"⟩,
  ⟨31, 168, 1, "8,3,23,1,113,1"⟩,
  ⟨31, 168, 2, "8,3,13,3,32,1"⟩,
  ⟨31, 168, 3, "0,1,8,1,16,1,260,1"⟩,
  ⟨30, 168, 0, "8,1,557,1"⟩,
  ⟨30, 168, 1, "8,2,13,4,23,1"⟩,
  ⟨30, 168, 2, "8,4,9,1,101,1"⟩,
  ⟨30, 168, 3, "0,1,8,1,17,1,260,1"⟩,
  ⟨29, 168, 0, "8,1,559,1"⟩,
  ⟨29, 168, 1, "8,1,13,4,51,1"⟩,
  ⟨29, 168, 2, "8,3,9,1,13,1,80,1"⟩,
  ⟨28, 168, 0, "13,7"⟩,
  ⟨28, 168, 1, "8,2,16,1,187,1"⟩,
  ⟨28, 168, 2, "8,2,9,1,23,1,101,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5598_mem, Shared.BasisChunk005.row5600_mem, Shared.BasisChunk005.row5601_mem, Shared.BasisChunk005.row5602_mem, Shared.BasisChunk005.row5604_mem, Shared.BasisChunk005.row5605_mem, Shared.BasisChunk005.row5606_mem, Shared.BasisChunk005.row5607_mem, Shared.BasisChunk005.row5608_mem, Shared.BasisChunk005.row5611_mem, Shared.BasisChunk005.row5613_mem, Shared.BasisChunk005.row5615_mem, Shared.BasisChunk005.row5616_mem, Shared.BasisChunk005.row5617_mem, Shared.BasisChunk005.row5619_mem, Shared.BasisChunk005.row5620_mem, Shared.BasisChunk005.row5621_mem, Shared.BasisChunk005.row5622_mem, Shared.BasisChunk005.row5623_mem, Shared.BasisChunk005.row5624_mem, Shared.BasisChunk005.row5625_mem, Shared.BasisChunk005.row5627_mem, Shared.BasisChunk005.row5629_mem, Shared.BasisChunk005.row5630_mem, Shared.BasisChunk005.row5631_mem, Shared.BasisChunk005.row5632_mem, Shared.BasisChunk005.row5633_mem, Shared.BasisChunk005.row5634_mem, Shared.BasisChunk005.row5635_mem, Shared.BasisChunk005.row5636_mem, Shared.BasisChunk005.row5638_mem, Shared.BasisChunk005.row5640_mem, Shared.BasisChunk005.row5641_mem, Shared.BasisChunk005.row5642_mem, Shared.BasisChunk005.row5643_mem, Shared.BasisChunk005.row5644_mem, Shared.BasisChunk005.row5645_mem, Shared.BasisChunk005.row5646_mem, Shared.BasisChunk005.row5647_mem, Shared.BasisChunk005.row5648_mem, Shared.BasisChunk005.row5649_mem, Shared.BasisChunk005.row5650_mem, Shared.BasisChunk005.row5651_mem, Shared.BasisChunk005.row5652_mem, Shared.BasisChunk005.row5653_mem, Shared.BasisChunk005.row5654_mem, Shared.BasisChunk005.row5655_mem, Shared.BasisChunk005.row5656_mem, Shared.BasisChunk005.row5657_mem, Shared.BasisChunk005.row5658_mem, Shared.BasisChunk005.row5659_mem, Shared.BasisChunk005.row5660_mem, Shared.BasisChunk005.row5661_mem, Shared.BasisChunk005.row5663_mem, Shared.BasisChunk005.row5664_mem, Shared.BasisChunk005.row5665_mem, Shared.BasisChunk005.row5666_mem, Shared.BasisChunk005.row5667_mem, Shared.BasisChunk005.row5668_mem, Shared.BasisChunk005.row5669_mem, Shared.BasisChunk005.row5670_mem, Shared.BasisChunk005.row5671_mem, Shared.BasisChunk005.row5672_mem, Shared.BasisChunk005.row5673_mem, Shared.BasisChunk005.row5674_mem, Shared.BasisChunk005.row5675_mem, Shared.BasisChunk005.row5676_mem, Shared.BasisChunk005.row5677_mem, Shared.BasisChunk005.row5678_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard073
