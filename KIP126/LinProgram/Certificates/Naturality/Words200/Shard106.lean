import KIP126.LinProgram.Generated.Naturality.Words200.Shard106
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk027
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk039
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk042
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk044
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard106
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard106
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation18_zero, Shared.RelationChunk000.relation22_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation44_zero, Shared.RelationChunk000.relation48_zero, Shared.RelationChunk000.relation49_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation74_zero, Shared.RelationChunk000.relation77_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation125_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation154_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk001.relation161_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation222_zero, Shared.RelationChunk002.relation229_zero, Shared.RelationChunk002.relation230_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk002.relation239_zero, Shared.RelationChunk002.relation240_zero, Shared.RelationChunk002.relation241_zero, Shared.RelationChunk003.relation271_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation326_zero, Shared.RelationChunk005.relation327_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk005.relation331_zero, Shared.RelationChunk005.relation332_zero, Shared.RelationChunk005.relation333_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation398_zero, Shared.RelationChunk007.relation420_zero, Shared.RelationChunk008.relation462_zero, Shared.RelationChunk009.relation489_zero, Shared.RelationChunk009.relation494_zero, Shared.RelationChunk009.relation495_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk011.relation584_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk014.relation735_zero, Shared.RelationChunk016.relation790_zero, Shared.RelationChunk016.relation792_zero, Shared.RelationChunk016.relation793_zero, Shared.RelationChunk016.relation794_zero, Shared.RelationChunk016.relation797_zero, Shared.RelationChunk016.relation798_zero, Shared.RelationChunk016.relation799_zero, Shared.RelationChunk016.relation800_zero, Shared.RelationChunk026.relation1124_zero, Shared.RelationChunk027.relation1145_zero, Shared.RelationChunk027.relation1146_zero, Shared.RelationChunk027.relation1148_zero, Shared.RelationChunk027.relation1150_zero, Shared.RelationChunk027.relation1151_zero, Shared.RelationChunk039.relation1559_zero, Shared.RelationChunk042.relation1629_zero, Shared.RelationChunk044.relation1664_zero, Shared.RelationChunk044.relation1665_zero, Shared.RelationChunk044.relation1666_zero, Shared.RelationChunk044.relation1667_zero, Shared.RelationChunk044.relation1668_zero, Shared.RelationChunk044.relation1669_zero, Shared.RelationChunk044.relation1670_zero, Shared.RelationChunk044.relation1671_zero, Shared.RelationChunk044.relation1672_zero, Shared.RelationChunk044.relation1673_zero, Shared.RelationChunk044.relation1674_zero, Shared.RelationChunk044.relation1675_zero, Shared.RelationChunk044.relation1676_zero, Shared.RelationChunk044.relation1677_zero, Shared.RelationChunk044.relation1678_zero, Shared.RelationChunk044.relation1679_zero, Shared.RelationChunk044.relation1680_zero, Shared.RelationChunk044.relation1681_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13570 128 := by cbv
private def targetRows : List BasisRow := [⟨50, 189, 1, "8,3,17,1,200,1"⟩,
  ⟨49, 189, 0, "16,1,636,1"⟩,
  ⟨49, 189, 1, "8,3,401,1"⟩,
  ⟨49, 189, 2, "0,1,969,1"⟩,
  ⟨48, 189, 0, "17,1,636,1"⟩,
  ⟨48, 189, 1, "8,6,116,1"⟩,
  ⟨47, 189, 0, "8,6,117,1"⟩,
  ⟨46, 189, 1, "8,5,17,1,78,1"⟩,
  ⟨45, 189, 0, "8,3,403,1"⟩,
  ⟨45, 189, 1, "8,5,171,1"⟩,
  ⟨44, 189, 0, "8,1,16,1,17,1,225,1"⟩,
  ⟨44, 189, 1, "8,8,39,1"⟩,
  ⟨43, 189, 0, "8,1,17,2,225,1"⟩,
  ⟨43, 189, 1, "8,8,40,1"⟩,
  ⟨42, 189, 0, "8,4,16,1,137,1"⟩,
  ⟨42, 189, 1, "8,7,17,1,20,1"⟩,
  ⟨41, 189, 0, "8,4,16,1,138,1"⟩,
  ⟨41, 189, 1, "8,7,63,1"⟩,
  ⟨40, 189, 1, "8,4,17,1,138,1"⟩,
  ⟨40, 189, 2, "8,8,9,1,13,1"⟩,
  ⟨39, 189, 0, "64,1,298,1"⟩,
  ⟨39, 189, 1, "8,3,42,1,137,1"⟩,
  ⟨39, 189, 2, "8,7,9,1,32,1"⟩,
  ⟨39, 189, 3, "0,1,8,1,759,1"⟩,
  ⟨38, 189, 0, "8,1,778,1"⟩,
  ⟨38, 189, 1, "8,6,9,1,13,1,23,1"⟩,
  ⟨38, 189, 2, "8,7,64,1"⟩,
  ⟨38, 189, 3, "0,1,17,1,623,1"⟩,
  ⟨37, 189, 0, "17,1,637,1"⟩,
  ⟨37, 189, 1, "8,5,9,1,13,1,51,1"⟩,
  ⟨37, 189, 2, "8,6,118,1"⟩,
  ⟨37, 189, 3, "0,1,971,1"⟩,
  ⟨37, 189, 4, "0,5,149,2"⟩,
  ⟨36, 189, 0, "8,2,64,1,146,1"⟩,
  ⟨36, 189, 1, "8,4,9,1,13,4"⟩,
  ⟨36, 189, 2, "8,5,17,1,80,1"⟩,
  ⟨36, 189, 3, "0,5,927,1"⟩,
  ⟨35, 189, 0, "8,2,64,1,147,1"⟩,
  ⟨35, 189, 1, "8,3,9,1,13,3,32,1"⟩,
  ⟨35, 189, 2, "8,5,173,1"⟩,
  ⟨35, 189, 3, "0,7,64,1,260,1"⟩,
  ⟨34, 189, 0, "8,2,9,1,13,4,23,1"⟩,
  ⟨34, 189, 1, "8,3,404,1"⟩,
  ⟨34, 189, 2, "8,5,13,1,101,1"⟩,
  ⟨34, 189, 3, "0,5,64,1,274,1"⟩,
  ⟨34, 189, 4, "0,7,897,1"⟩,
  ⟨33, 189, 0, "8,1,9,1,13,4,51,1"⟩,
  ⟨33, 189, 1, "8,2,580,1"⟩,
  ⟨33, 189, 2, "8,4,13,2,80,1"⟩,
  ⟨33, 189, 3, "0,6,921,1"⟩,
  ⟨33, 189, 4, "0,6,919,1"⟩,
  ⟨32, 189, 0, "9,1,13,7"⟩,
  ⟨32, 189, 1, "8,3,13,1,23,1,101,1"⟩,
  ⟨32, 189, 2, "8,4,254,1"⟩,
  ⟨32, 189, 3, "0,7,898,1"⟩,
  ⟨31, 189, 0, "8,2,13,2,23,1,80,1"⟩,
  ⟨31, 189, 1, "8,4,255,1"⟩,
  ⟨30, 189, 1, "8,1,13,4,101,1"⟩,
  ⟨30, 189, 2, "8,3,20,1,188,1"⟩,
  ⟨29, 189, 0, "64,1,299,1"⟩,
  ⟨29, 189, 1, "13,5,80,1"⟩,
  ⟨29, 189, 2, "8,2,20,1,267,1"⟩,
  ⟨29, 189, 3, "0,1,16,1,627,1"⟩,
  ⟨28, 189, 0, "997,1"⟩,
  ⟨28, 189, 1, "138,1,188,1"⟩,
  ⟨28, 189, 2, "8,2,9,1,13,1,212,1"⟩,
  ⟨28, 189, 3, "0,1,17,1,627,1"⟩,
  ⟨28, 189, 4, "0,2,963,1"⟩,
  ⟨27, 189, 0, "64,1,301,1"⟩,
  ⟨27, 189, 1, "8,1,779,1"⟩,
  ⟨27, 189, 2, "8,1,9,1,13,2,188,1"⟩,
  ⟨27, 189, 4, "0,1,974,1"⟩,
  ⟨27, 189, 5, "0,1,973,1"⟩,
  ⟨26, 189, 0, "9,1,13,2,267,1"⟩,
  ⟨26, 189, 1, "8,1,64,1,212,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row8090_mem, Shared.BasisChunk007.row8091_mem, Shared.BasisChunk007.row8092_mem, Shared.BasisChunk007.row8093_mem, Shared.BasisChunk007.row8094_mem, Shared.BasisChunk007.row8095_mem, Shared.BasisChunk007.row8096_mem, Shared.BasisChunk007.row8098_mem, Shared.BasisChunk007.row8099_mem, Shared.BasisChunk007.row8100_mem, Shared.BasisChunk007.row8101_mem, Shared.BasisChunk007.row8102_mem, Shared.BasisChunk007.row8103_mem, Shared.BasisChunk007.row8104_mem, Shared.BasisChunk007.row8105_mem, Shared.BasisChunk007.row8106_mem, Shared.BasisChunk007.row8107_mem, Shared.BasisChunk007.row8108_mem, Shared.BasisChunk007.row8110_mem, Shared.BasisChunk007.row8111_mem, Shared.BasisChunk007.row8112_mem, Shared.BasisChunk007.row8113_mem, Shared.BasisChunk007.row8114_mem, Shared.BasisChunk007.row8115_mem, Shared.BasisChunk007.row8116_mem, Shared.BasisChunk007.row8117_mem, Shared.BasisChunk007.row8118_mem, Shared.BasisChunk007.row8119_mem, Shared.BasisChunk007.row8120_mem, Shared.BasisChunk007.row8121_mem, Shared.BasisChunk007.row8122_mem, Shared.BasisChunk007.row8123_mem, Shared.BasisChunk007.row8124_mem, Shared.BasisChunk007.row8125_mem, Shared.BasisChunk007.row8126_mem, Shared.BasisChunk007.row8127_mem, Shared.BasisChunk007.row8128_mem, Shared.BasisChunk007.row8129_mem, Shared.BasisChunk007.row8130_mem, Shared.BasisChunk007.row8131_mem, Shared.BasisChunk007.row8132_mem, Shared.BasisChunk007.row8133_mem, Shared.BasisChunk007.row8134_mem, Shared.BasisChunk007.row8135_mem, Shared.BasisChunk007.row8136_mem, Shared.BasisChunk007.row8137_mem, Shared.BasisChunk007.row8138_mem, Shared.BasisChunk007.row8139_mem, Shared.BasisChunk007.row8140_mem, Shared.BasisChunk007.row8141_mem, Shared.BasisChunk007.row8142_mem, Shared.BasisChunk007.row8143_mem, Shared.BasisChunk007.row8144_mem, Shared.BasisChunk007.row8145_mem, Shared.BasisChunk007.row8146_mem, Shared.BasisChunk007.row8147_mem, Shared.BasisChunk007.row8148_mem, Shared.BasisChunk007.row8150_mem, Shared.BasisChunk007.row8151_mem, Shared.BasisChunk007.row8152_mem, Shared.BasisChunk007.row8153_mem, Shared.BasisChunk007.row8154_mem, Shared.BasisChunk007.row8155_mem, Shared.BasisChunk007.row8156_mem, Shared.BasisChunk007.row8157_mem, Shared.BasisChunk007.row8158_mem, Shared.BasisChunk007.row8159_mem, Shared.BasisChunk007.row8160_mem, Shared.BasisChunk007.row8161_mem, Shared.BasisChunk007.row8162_mem, Shared.BasisChunk007.row8163_mem, Shared.BasisChunk007.row8165_mem, Shared.BasisChunk007.row8166_mem, Shared.BasisChunk007.row8167_mem, Shared.BasisChunk007.row8168_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard106
