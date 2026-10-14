module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard069
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard069
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard069
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation18_zero, Shared.RelationChunk000.relation22_zero, Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation44_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation218_zero, Shared.RelationChunk002.relation220_zero, Shared.RelationChunk002.relation221_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk004.relation293_zero, Shared.RelationChunk004.relation295_zero, Shared.RelationChunk004.relation296_zero, Shared.RelationChunk004.relation297_zero, Shared.RelationChunk004.relation298_zero, Shared.RelationChunk005.relation328_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation406_zero, Shared.RelationChunk007.relation419_zero, Shared.RelationChunk007.relation420_zero, Shared.RelationChunk007.relation423_zero, Shared.RelationChunk007.relation425_zero, Shared.RelationChunk007.relation427_zero, Shared.RelationChunk007.relation428_zero, Shared.RelationChunk007.relation429_zero, Shared.RelationChunk007.relation430_zero, Shared.RelationChunk009.relation492_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk011.relation581_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk013.relation678_zero, Shared.RelationChunk013.relation682_zero, Shared.RelationChunk013.relation685_zero, Shared.RelationChunk013.relation686_zero, Shared.RelationChunk013.relation687_zero, Shared.RelationChunk021.relation966_zero, Shared.RelationChunk022.relation978_zero, Shared.RelationChunk022.relation992_zero, Shared.RelationChunk022.relation993_zero, Shared.RelationChunk022.relation994_zero, Shared.RelationChunk022.relation995_zero, Shared.RelationChunk022.relation996_zero, Shared.RelationChunk022.relation997_zero, Shared.RelationChunk022.relation998_zero, Shared.RelationChunk022.relation999_zero, Shared.RelationChunk022.relation1000_zero, Shared.RelationChunk022.relation1001_zero, Shared.RelationChunk023.relation1002_zero, Shared.RelationChunk023.relation1003_zero, Shared.RelationChunk023.relation1004_zero, Shared.RelationChunk023.relation1005_zero, Shared.RelationChunk023.relation1006_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8834 128 := by cbv
private def targetRows : List BasisRow := [⟨8, 164, 3, "22,1,324,1"⟩,
  ⟨8, 164, 4, "0,3,660,1"⟩,
  ⟨7, 164, 1, "24,1,69,2"⟩,
  ⟨7, 164, 2, "23,1,324,1"⟩,
  ⟨6, 164, 1, "24,1,324,1"⟩,
  ⟨6, 164, 2, "0,4,18,1,324,1"⟩,
  ⟨3, 164, 0, "2,1,18,1,324,1"⟩,
  ⟨165, 165, 0, "0,165"⟩,
  ⟨54, 165, 0, "0,9,606,1"⟩,
  ⟨51, 165, 0, "701,1"⟩,
  ⟨48, 165, 1, "0,6,635,1"⟩,
  ⟨47, 165, 0, "8,2,326,1"⟩,
  ⟨47, 165, 1, "0,6,636,1"⟩,
  ⟨46, 165, 0, "8,1,17,1,253,1"⟩,
  ⟨45, 165, 0, "8,1,528,1"⟩,
  ⟨45, 165, 1, "0,3,662,1"⟩,
  ⟨44, 165, 0, "8,4,152,1"⟩,
  ⟨43, 165, 0, "8,4,153,1"⟩,
  ⟨42, 165, 1, "8,3,17,1,117,1"⟩,
  ⟨41, 165, 0, "16,1,403,1"⟩,
  ⟨41, 165, 1, "8,3,223,1"⟩,
  ⟨41, 165, 2, "0,1,685,1"⟩,
  ⟨40, 165, 0, "17,1,403,1"⟩,
  ⟨40, 165, 1, "8,6,55,1"⟩,
  ⟨39, 165, 0, "8,6,56,1"⟩,
  ⟨39, 165, 1, "0,1,686,1"⟩,
  ⟨38, 165, 1, "8,5,17,1,40,1"⟩,
  ⟨38, 165, 2, "0,37,324,1"⟩,
  ⟨37, 165, 0, "8,3,225,1"⟩,
  ⟨37, 165, 1, "8,5,100,1"⟩,
  ⟨36, 165, 0, "8,1,16,1,17,1,138,1"⟩,
  ⟨36, 165, 1, "8,8,9,1"⟩,
  ⟨35, 165, 0, "8,1,17,2,138,1"⟩,
  ⟨35, 165, 1, "8,7,29,1"⟩,
  ⟨34, 165, 0, "8,4,16,1,64,1"⟩,
  ⟨34, 165, 1, "8,6,9,1,23,1"⟩,
  ⟨33, 165, 0, "8,4,17,1,64,1"⟩,
  ⟨33, 165, 1, "8,5,9,1,51,1"⟩,
  ⟨32, 165, 1, "8,4,154,1"⟩,
  ⟨32, 165, 2, "8,4,9,1,13,3"⟩,
  ⟨31, 165, 0, "64,1,185,1"⟩,
  ⟨31, 165, 1, "8,3,42,1,64,1"⟩,
  ⟨31, 165, 2, "8,3,9,1,13,2,32,1"⟩,
  ⟨31, 165, 3, "0,1,8,1,516,1"⟩,
  ⟨30, 165, 0, "8,1,529,1"⟩,
  ⟨30, 165, 1, "8,2,9,1,13,3,23,1"⟩,
  ⟨30, 165, 2, "8,5,101,1"⟩,
  ⟨30, 165, 3, "0,1,17,1,380,1"⟩,
  ⟨29, 165, 0, "17,1,404,1"⟩,
  ⟨29, 165, 1, "8,1,9,1,13,3,51,1"⟩,
  ⟨29, 165, 2, "8,4,13,1,80,1"⟩,
  ⟨29, 165, 3, "0,1,688,1"⟩,
  ⟨29, 165, 4, "0,5,642,1"⟩,
  ⟨28, 165, 0, "9,1,13,6"⟩,
  ⟨28, 165, 1, "8,2,64,1,72,1"⟩,
  ⟨28, 165, 2, "8,3,23,1,101,1"⟩,
  ⟨28, 165, 3, "0,4,654,1"⟩,
  ⟨27, 165, 0, "8,2,327,1"⟩,
  ⟨27, 165, 1, "8,2,13,1,23,1,80,1"⟩,
  ⟨27, 165, 2, "0,7,627,1"⟩,
  ⟨26, 165, 0, "8,1,17,1,255,1"⟩,
  ⟨26, 165, 1, "8,1,13,3,101,1"⟩,
  ⟨26, 165, 2, "0,5,645,1"⟩,
  ⟨26, 165, 3, "0,5,644,1"⟩,
  ⟨25, 165, 0, "13,4,80,1"⟩,
  ⟨25, 165, 1, "8,1,530,1"⟩,
  ⟨25, 165, 2, "0,5,646,1"⟩,
  ⟨24, 165, 0, "8,2,9,1,212,1"⟩,
  ⟨23, 165, 0, "8,1,9,1,13,1,188,1"⟩,
  ⟨22, 165, 1, "9,1,13,1,267,1"⟩,
  ⟨22, 165, 2, "0,1,2,1,646,1"⟩,
  ⟨21, 165, 1, "64,1,188,1"⟩,
  ⟨21, 165, 2, "13,1,472,1"⟩,
  ⟨21, 165, 3, "0,1,690,1"⟩,
  ⟨20, 165, 0, "704,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5296_mem, Shared.BasisChunk005.row5297_mem, Shared.BasisChunk005.row5299_mem, Shared.BasisChunk005.row5300_mem, Shared.BasisChunk005.row5303_mem, Shared.BasisChunk005.row5304_mem, Shared.BasisChunk005.row5307_mem, Shared.BasisChunk005.row5308_mem, Shared.BasisChunk005.row5309_mem, Shared.BasisChunk005.row5311_mem, Shared.BasisChunk005.row5313_mem, Shared.BasisChunk005.row5314_mem, Shared.BasisChunk005.row5315_mem, Shared.BasisChunk005.row5316_mem, Shared.BasisChunk005.row5317_mem, Shared.BasisChunk005.row5318_mem, Shared.BasisChunk005.row5319_mem, Shared.BasisChunk005.row5320_mem, Shared.BasisChunk005.row5322_mem, Shared.BasisChunk005.row5323_mem, Shared.BasisChunk005.row5324_mem, Shared.BasisChunk005.row5325_mem, Shared.BasisChunk005.row5326_mem, Shared.BasisChunk005.row5327_mem, Shared.BasisChunk005.row5328_mem, Shared.BasisChunk005.row5329_mem, Shared.BasisChunk005.row5331_mem, Shared.BasisChunk005.row5332_mem, Shared.BasisChunk005.row5333_mem, Shared.BasisChunk005.row5334_mem, Shared.BasisChunk005.row5335_mem, Shared.BasisChunk005.row5336_mem, Shared.BasisChunk005.row5337_mem, Shared.BasisChunk005.row5338_mem, Shared.BasisChunk005.row5339_mem, Shared.BasisChunk005.row5340_mem, Shared.BasisChunk005.row5341_mem, Shared.BasisChunk005.row5342_mem, Shared.BasisChunk005.row5344_mem, Shared.BasisChunk005.row5345_mem, Shared.BasisChunk005.row5346_mem, Shared.BasisChunk005.row5347_mem, Shared.BasisChunk005.row5348_mem, Shared.BasisChunk005.row5349_mem, Shared.BasisChunk005.row5350_mem, Shared.BasisChunk005.row5351_mem, Shared.BasisChunk005.row5352_mem, Shared.BasisChunk005.row5353_mem, Shared.BasisChunk005.row5354_mem, Shared.BasisChunk005.row5355_mem, Shared.BasisChunk005.row5356_mem, Shared.BasisChunk005.row5357_mem, Shared.BasisChunk005.row5358_mem, Shared.BasisChunk005.row5359_mem, Shared.BasisChunk005.row5360_mem, Shared.BasisChunk005.row5361_mem, Shared.BasisChunk005.row5362_mem, Shared.BasisChunk005.row5363_mem, Shared.BasisChunk005.row5364_mem, Shared.BasisChunk005.row5365_mem, Shared.BasisChunk005.row5366_mem, Shared.BasisChunk005.row5367_mem, Shared.BasisChunk005.row5368_mem, Shared.BasisChunk005.row5369_mem, Shared.BasisChunk005.row5370_mem, Shared.BasisChunk005.row5371_mem, Shared.BasisChunk005.row5372_mem, Shared.BasisChunk005.row5373_mem, Shared.BasisChunk005.row5374_mem, Shared.BasisChunk005.row5376_mem, Shared.BasisChunk005.row5377_mem, Shared.BasisChunk005.row5379_mem, Shared.BasisChunk005.row5380_mem, Shared.BasisChunk005.row5381_mem, Shared.BasisChunk005.row5382_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard069
