module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard065
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard065
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard065
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation19_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation110_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation193_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk001.relation198_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation238_zero, Shared.RelationChunk003.relation278_zero, Shared.RelationChunk003.relation279_zero, Shared.RelationChunk003.relation280_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation284_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation393_zero, Shared.RelationChunk006.relation395_zero, Shared.RelationChunk006.relation396_zero, Shared.RelationChunk006.relation397_zero, Shared.RelationChunk006.relation399_zero, Shared.RelationChunk006.relation400_zero, Shared.RelationChunk006.relation405_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk010.relation534_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk012.relation623_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk012.relation626_zero, Shared.RelationChunk012.relation630_zero, Shared.RelationChunk012.relation634_zero, Shared.RelationChunk012.relation635_zero, Shared.RelationChunk012.relation638_zero, Shared.RelationChunk020.relation934_zero, Shared.RelationChunk020.relation935_zero, Shared.RelationChunk020.relation942_zero, Shared.RelationChunk021.relation945_zero, Shared.RelationChunk021.relation946_zero, Shared.RelationChunk021.relation947_zero, Shared.RelationChunk021.relation948_zero, Shared.RelationChunk021.relation953_zero, Shared.RelationChunk021.relation955_zero, Shared.RelationChunk021.relation956_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8322 128 := by cbv
private def targetRows : List BasisRow := [⟨8, 161, 1, "20,1,324,1"⟩,
  ⟨7, 161, 0, "0,1,7,1,507,1"⟩,
  ⟨6, 161, 0, "0,1,7,1,508,1"⟩,
  ⟨4, 161, 0, "0,1,7,2,324,1"⟩,
  ⟨3, 161, 0, "0,1,18,1,324,1"⟩,
  ⟨162, 162, 0, "0,162"⟩,
  ⟨55, 162, 0, "0,2,641,1"⟩,
  ⟨51, 162, 0, "0,6,606,1"⟩,
  ⟨47, 162, 0, "8,2,296,1"⟩,
  ⟨46, 162, 0, "16,1,17,1,183,1"⟩,
  ⟨45, 162, 0, "8,1,498,1"⟩,
  ⟨45, 162, 1, "0,3,635,1"⟩,
  ⟨44, 162, 0, "8,4,145,1"⟩,
  ⟨44, 162, 1, "0,3,636,1"⟩,
  ⟨43, 162, 0, "8,3,16,1,111,1"⟩,
  ⟨42, 162, 1, "8,3,17,1,111,1"⟩,
  ⟨41, 162, 0, "663,1"⟩,
  ⟨41, 162, 1, "8,3,211,1"⟩,
  ⟨40, 162, 0, "8,6,49,1"⟩,
  ⟨39, 162, 0, "8,6,50,1"⟩,
  ⟨38, 162, 1, "8,4,16,1,17,2"⟩,
  ⟨37, 162, 0, "8,2,298,1"⟩,
  ⟨37, 162, 1, "8,5,88,1"⟩,
  ⟨36, 162, 0, "8,1,17,1,238,1"⟩,
  ⟨36, 162, 1, "8,9"⟩,
  ⟨36, 162, 2, "0,18,500,1"⟩,
  ⟨35, 162, 0, "17,2,185,1"⟩,
  ⟨35, 162, 1, "8,7,22,1"⟩,
  ⟨35, 162, 2, "0,34,324,1"⟩,
  ⟨34, 162, 0, "8,4,146,1"⟩,
  ⟨34, 162, 1, "8,7,23,1"⟩,
  ⟨33, 162, 0, "8,4,147,1"⟩,
  ⟨33, 162, 1, "8,6,51,1"⟩,
  ⟨32, 162, 0, "8,3,17,1,113,1"⟩,
  ⟨32, 162, 1, "8,5,13,3"⟩,
  ⟨31, 162, 0, "8,2,17,1,162,1"⟩,
  ⟨31, 162, 1, "8,4,13,2,32,1"⟩,
  ⟨31, 162, 2, "0,1,8,1,491,1"⟩,
  ⟨30, 162, 0, "664,1"⟩,
  ⟨30, 162, 1, "8,3,13,3,23,1"⟩,
  ⟨30, 162, 2, "8,5,89,1"⟩,
  ⟨29, 162, 1, "8,2,13,3,51,1"⟩,
  ⟨29, 162, 2, "8,4,9,1,80,1"⟩,
  ⟨28, 162, 0, "8,1,13,6"⟩,
  ⟨28, 162, 1, "8,2,64,2"⟩,
  ⟨28, 162, 2, "8,3,23,1,89,1"⟩,
  ⟨27, 162, 0, "13,5,32,1"⟩,
  ⟨27, 162, 1, "8,2,299,1"⟩,
  ⟨27, 162, 2, "8,2,9,1,23,1,80,1"⟩,
  ⟨27, 162, 3, "0,1,8,2,291,1"⟩,
  ⟨26, 162, 0, "13,5,33,1"⟩,
  ⟨26, 162, 1, "8,1,499,1"⟩,
  ⟨26, 162, 2, "8,1,9,1,13,2,101,1"⟩,
  ⟨26, 162, 3, "0,1,8,2,292,1"⟩,
  ⟨26, 162, 4, "0,2,642,1"⟩,
  ⟨25, 162, 0, "13,1,435,1"⟩,
  ⟨25, 162, 1, "9,1,13,3,80,1"⟩,
  ⟨25, 162, 3, "0,1,654,1"⟩,
  ⟨24, 162, 0, "8,3,212,1"⟩,
  ⟨24, 162, 1, "0,2,643,1"⟩,
  ⟨24, 162, 2, "0,4,627,1"⟩,
  ⟨23, 162, 0, "8,2,13,1,188,1"⟩,
  ⟨23, 162, 1, "0,2,645,1"⟩,
  ⟨23, 162, 2, "0,2,644,1"⟩,
  ⟨22, 162, 0, "23,1,303,1"⟩,
  ⟨22, 162, 1, "8,1,13,1,267,1"⟩,
  ⟨22, 162, 3, "0,2,646,1"⟩,
  ⟨22, 162, 4, "0,10,575,1"⟩,
  ⟨21, 162, 1, "13,1,23,1,188,1"⟩,
  ⟨21, 162, 2, "9,1,472,1"⟩,
  ⟨21, 162, 3, "1,1,646,1"⟩,
  ⟨21, 162, 4, "0,1,655,1"⟩,
  ⟨20, 162, 0, "667,1"⟩,
  ⟨20, 162, 1, "13,1,23,1,189,1"⟩,
  ⟨20, 162, 2, "1,2,628,1"⟩,
  ⟨20, 162, 3, "0,2,8,1,69,1,113,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row5001_mem, Shared.BasisChunk004.row5002_mem, Shared.BasisChunk004.row5003_mem, Shared.BasisChunk004.row5005_mem, Shared.BasisChunk004.row5006_mem, Shared.BasisChunk004.row5007_mem, Shared.BasisChunk004.row5008_mem, Shared.BasisChunk004.row5010_mem, Shared.BasisChunk004.row5012_mem, Shared.BasisChunk004.row5013_mem, Shared.BasisChunk004.row5014_mem, Shared.BasisChunk004.row5015_mem, Shared.BasisChunk004.row5016_mem, Shared.BasisChunk004.row5017_mem, Shared.BasisChunk004.row5018_mem, Shared.BasisChunk004.row5020_mem, Shared.BasisChunk004.row5021_mem, Shared.BasisChunk004.row5022_mem, Shared.BasisChunk004.row5023_mem, Shared.BasisChunk004.row5024_mem, Shared.BasisChunk004.row5026_mem, Shared.BasisChunk004.row5027_mem, Shared.BasisChunk004.row5028_mem, Shared.BasisChunk004.row5029_mem, Shared.BasisChunk004.row5030_mem, Shared.BasisChunk004.row5031_mem, Shared.BasisChunk004.row5032_mem, Shared.BasisChunk004.row5033_mem, Shared.BasisChunk004.row5034_mem, Shared.BasisChunk004.row5035_mem, Shared.BasisChunk004.row5036_mem, Shared.BasisChunk004.row5037_mem, Shared.BasisChunk004.row5038_mem, Shared.BasisChunk004.row5039_mem, Shared.BasisChunk004.row5040_mem, Shared.BasisChunk004.row5041_mem, Shared.BasisChunk004.row5042_mem, Shared.BasisChunk004.row5043_mem, Shared.BasisChunk004.row5044_mem, Shared.BasisChunk004.row5045_mem, Shared.BasisChunk004.row5046_mem, Shared.BasisChunk004.row5048_mem, Shared.BasisChunk004.row5049_mem, Shared.BasisChunk004.row5050_mem, Shared.BasisChunk004.row5051_mem, Shared.BasisChunk004.row5052_mem, Shared.BasisChunk004.row5053_mem, Shared.BasisChunk004.row5054_mem, Shared.BasisChunk004.row5055_mem, Shared.BasisChunk004.row5056_mem, Shared.BasisChunk004.row5057_mem, Shared.BasisChunk004.row5058_mem, Shared.BasisChunk004.row5059_mem, Shared.BasisChunk004.row5060_mem, Shared.BasisChunk004.row5061_mem, Shared.BasisChunk004.row5062_mem, Shared.BasisChunk004.row5063_mem, Shared.BasisChunk004.row5065_mem, Shared.BasisChunk004.row5066_mem, Shared.BasisChunk004.row5067_mem, Shared.BasisChunk004.row5068_mem, Shared.BasisChunk004.row5069_mem, Shared.BasisChunk004.row5070_mem, Shared.BasisChunk004.row5071_mem, Shared.BasisChunk004.row5072_mem, Shared.BasisChunk004.row5073_mem, Shared.BasisChunk004.row5075_mem, Shared.BasisChunk004.row5076_mem, Shared.BasisChunk004.row5078_mem, Shared.BasisChunk004.row5079_mem, Shared.BasisChunk004.row5080_mem, Shared.BasisChunk004.row5081_mem, Shared.BasisChunk004.row5082_mem, Shared.BasisChunk004.row5083_mem, Shared.BasisChunk004.row5084_mem, Shared.BasisChunk004.row5085_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard065
