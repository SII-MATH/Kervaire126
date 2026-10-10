import KIP126.LinProgram.Generated.Naturality.Words200.Shard116
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk049
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk050
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk051
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard116
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard116
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
  exact ⟨Shared.RelationChunk000.relation6_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk000.relation125_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation150_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation168_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation181_zero, Shared.RelationChunk001.relation182_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation272_zero, Shared.RelationChunk003.relation274_zero, Shared.RelationChunk003.relation275_zero, Shared.RelationChunk006.relation367_zero, Shared.RelationChunk006.relation368_zero, Shared.RelationChunk006.relation369_zero, Shared.RelationChunk006.relation370_zero, Shared.RelationChunk006.relation371_zero, Shared.RelationChunk006.relation372_zero, Shared.RelationChunk006.relation377_zero, Shared.RelationChunk006.relation378_zero, Shared.RelationChunk006.relation379_zero, Shared.RelationChunk007.relation426_zero, Shared.RelationChunk008.relation455_zero, Shared.RelationChunk011.relation584_zero, Shared.RelationChunk011.relation585_zero, Shared.RelationChunk011.relation586_zero, Shared.RelationChunk011.relation587_zero, Shared.RelationChunk019.relation900_zero, Shared.RelationChunk019.relation901_zero, Shared.RelationChunk019.relation903_zero, Shared.RelationChunk019.relation904_zero, Shared.RelationChunk019.relation905_zero, Shared.RelationChunk019.relation906_zero, Shared.RelationChunk023.relation1003_zero, Shared.RelationChunk029.relation1264_zero, Shared.RelationChunk032.relation1342_zero, Shared.RelationChunk032.relation1343_zero, Shared.RelationChunk032.relation1346_zero, Shared.RelationChunk032.relation1347_zero, Shared.RelationChunk032.relation1348_zero, Shared.RelationChunk032.relation1349_zero, Shared.RelationChunk049.relation1764_zero, Shared.RelationChunk050.relation1788_zero, Shared.RelationChunk051.relation1807_zero, Shared.RelationChunk051.relation1808_zero, Shared.RelationChunk051.relation1809_zero, Shared.RelationChunk051.relation1810_zero, Shared.RelationChunk051.relation1811_zero, Shared.RelationChunk051.relation1812_zero, Shared.RelationChunk051.relation1813_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14850 128 := by cbv
private def targetRows : List BasisRow := [⟨14, 194, 2, "8,1,42,1,324,1"⟩,
  ⟨14, 194, 4, "0,3,64,1,324,1"⟩,
  ⟨13, 194, 0, "1091,1"⟩,
  ⟨13, 194, 1, "8,1,13,2,324,1"⟩,
  ⟨13, 194, 2, "0,2,66,1,324,1"⟩,
  ⟨12, 194, 0, "13,1,32,1,324,1"⟩,
  ⟨12, 194, 1, "0,1,18,2,333,1"⟩,
  ⟨11, 194, 1, "13,1,33,1,324,1"⟩,
  ⟨11, 194, 2, "0,1,18,1,659,1"⟩,
  ⟨10, 194, 0, "0,1,18,1,20,1,324,1"⟩,
  ⟨10, 194, 1, "0,2,67,1,324,1"⟩,
  ⟨9, 194, 0, "0,2,68,1,324,1"⟩,
  ⟨7, 194, 0, "0,1,18,1,660,1"⟩,
  ⟨6, 194, 0, "18,2,341,1"⟩,
  ⟨6, 194, 1, "0,2,1058,1"⟩,
  ⟨5, 194, 1, "0,2,18,2,324,1"⟩,
  ⟨195, 195, 0, "0,195"⟩,
  ⟨59, 195, 0, "8,1,852,1"⟩,
  ⟨58, 195, 0, "17,1,701,1"⟩,
  ⟨57, 195, 0, "1092,1"⟩,
  ⟨56, 195, 0, "8,3,469,1"⟩,
  ⟨55, 195, 0, "8,3,470,1"⟩,
  ⟨54, 195, 0, "8,2,17,1,326,1"⟩,
  ⟨53, 195, 0, "8,2,634,1"⟩,
  ⟨52, 195, 0, "8,5,199,1"⟩,
  ⟨51, 195, 0, "8,5,200,1"⟩,
  ⟨50, 195, 1, "8,4,17,1,153,1"⟩,
  ⟨49, 195, 0, "8,2,636,1"⟩,
  ⟨49, 195, 1, "8,4,283,1"⟩,
  ⟨49, 195, 2, "0,1,16,1,685,1"⟩,
  ⟨48, 195, 0, "16,1,17,1,403,1"⟩,
  ⟨48, 195, 1, "8,7,77,1"⟩,
  ⟨48, 195, 2, "0,1,17,1,685,1"⟩,
  ⟨47, 195, 1, "17,2,403,1"⟩,
  ⟨47, 195, 2, "8,7,78,1"⟩,
  ⟨46, 195, 0, "8,3,16,1,224,1"⟩,
  ⟨46, 195, 1, "8,6,17,1,56,1"⟩,
  ⟨46, 195, 2, "0,4,1033,1"⟩,
  ⟨45, 195, 0, "8,3,16,1,225,1"⟩,
  ⟨45, 195, 1, "8,6,136,1"⟩,
  ⟨45, 195, 2, "0,2,1059,1"⟩,
  ⟨44, 195, 0, "8,3,17,1,225,1"⟩,
  ⟨44, 195, 1, "8,9,19,1"⟩,
  ⟨43, 195, 0, "8,2,42,1,224,1"⟩,
  ⟨43, 195, 1, "8,9,20,1"⟩,
  ⟨43, 195, 2, "0,1,1076,1"⟩,
  ⟨42, 195, 0, "1093,1"⟩,
  ⟨42, 195, 1, "8,6,137,1"⟩,
  ⟨42, 195, 2, "8,8,45,1"⟩,
  ⟨41, 195, 0, "8,6,138,1"⟩,
  ⟨41, 195, 1, "8,8,46,1"⟩,
  ⟨40, 195, 0, "8,1,64,1,237,1"⟩,
  ⟨40, 195, 1, "8,4,16,1,154,1"⟩,
  ⟨40, 195, 2, "8,7,9,1,13,2"⟩,
  ⟨40, 195, 3, "1,1,5,1,64,1,244,1"⟩,
  ⟨39, 195, 0, "8,1,64,1,238,1"⟩,
  ⟨39, 195, 1, "8,4,17,1,154,1"⟩,
  ⟨39, 195, 2, "8,6,9,1,13,1,32,1"⟩,
  ⟨39, 195, 3, "0,1,8,2,623,1"⟩,
  ⟨39, 195, 4, "0,12,919,1"⟩,
  ⟨38, 195, 0, "8,2,637,1"⟩,
  ⟨38, 195, 1, "8,5,9,1,13,2,23,1"⟩,
  ⟨38, 195, 2, "8,7,79,1"⟩,
  ⟨38, 195, 3, "0,1,8,1,17,1,516,1"⟩,
  ⟨38, 195, 4, "0,13,898,1"⟩,
  ⟨37, 195, 0, "8,1,17,1,529,1"⟩,
  ⟨37, 195, 1, "8,4,9,1,13,2,51,1"⟩,
  ⟨37, 195, 2, "8,7,80,1"⟩,
  ⟨37, 195, 3, "0,1,17,2,380,1"⟩,
  ⟨36, 195, 0, "8,3,64,1,112,1"⟩,
  ⟨36, 195, 1, "8,3,9,1,13,5"⟩,
  ⟨36, 195, 2, "8,5,22,1,80,1"⟩,
  ⟨36, 195, 3, "0,6,64,3"⟩,
  ⟨35, 195, 0, "8,2,9,1,13,4,32,1"⟩,
  ⟨35, 195, 1, "8,3,64,1,113,1"⟩,
  ⟨35, 195, 2, "8,5,23,1,80,1"⟩,
  ⟨35, 195, 3, "0,6,64,1,299,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8828_mem, Shared.BasisChunk008.row8830_mem, Shared.BasisChunk008.row8831_mem, Shared.BasisChunk008.row8832_mem, Shared.BasisChunk008.row8833_mem, Shared.BasisChunk008.row8834_mem, Shared.BasisChunk008.row8835_mem, Shared.BasisChunk008.row8837_mem, Shared.BasisChunk008.row8838_mem, Shared.BasisChunk008.row8839_mem, Shared.BasisChunk008.row8840_mem, Shared.BasisChunk008.row8841_mem, Shared.BasisChunk008.row8842_mem, Shared.BasisChunk008.row8843_mem, Shared.BasisChunk008.row8844_mem, Shared.BasisChunk008.row8846_mem, Shared.BasisChunk008.row8848_mem, Shared.BasisChunk008.row8850_mem, Shared.BasisChunk008.row8851_mem, Shared.BasisChunk008.row8852_mem, Shared.BasisChunk008.row8853_mem, Shared.BasisChunk008.row8854_mem, Shared.BasisChunk008.row8855_mem, Shared.BasisChunk008.row8856_mem, Shared.BasisChunk008.row8857_mem, Shared.BasisChunk008.row8858_mem, Shared.BasisChunk008.row8860_mem, Shared.BasisChunk008.row8861_mem, Shared.BasisChunk008.row8862_mem, Shared.BasisChunk008.row8863_mem, Shared.BasisChunk008.row8864_mem, Shared.BasisChunk008.row8865_mem, Shared.BasisChunk008.row8866_mem, Shared.BasisChunk008.row8868_mem, Shared.BasisChunk008.row8869_mem, Shared.BasisChunk008.row8870_mem, Shared.BasisChunk008.row8871_mem, Shared.BasisChunk008.row8872_mem, Shared.BasisChunk008.row8873_mem, Shared.BasisChunk008.row8874_mem, Shared.BasisChunk008.row8875_mem, Shared.BasisChunk008.row8876_mem, Shared.BasisChunk008.row8877_mem, Shared.BasisChunk008.row8879_mem, Shared.BasisChunk008.row8880_mem, Shared.BasisChunk008.row8881_mem, Shared.BasisChunk008.row8882_mem, Shared.BasisChunk008.row8883_mem, Shared.BasisChunk008.row8884_mem, Shared.BasisChunk008.row8885_mem, Shared.BasisChunk008.row8886_mem, Shared.BasisChunk008.row8887_mem, Shared.BasisChunk008.row8888_mem, Shared.BasisChunk008.row8889_mem, Shared.BasisChunk008.row8890_mem, Shared.BasisChunk008.row8891_mem, Shared.BasisChunk008.row8892_mem, Shared.BasisChunk008.row8893_mem, Shared.BasisChunk008.row8894_mem, Shared.BasisChunk008.row8895_mem, Shared.BasisChunk008.row8896_mem, Shared.BasisChunk008.row8897_mem, Shared.BasisChunk008.row8898_mem, Shared.BasisChunk008.row8899_mem, Shared.BasisChunk008.row8900_mem, Shared.BasisChunk008.row8901_mem, Shared.BasisChunk008.row8902_mem, Shared.BasisChunk008.row8903_mem, Shared.BasisChunk008.row8904_mem, Shared.BasisChunk008.row8905_mem, Shared.BasisChunk008.row8906_mem, Shared.BasisChunk008.row8907_mem, Shared.BasisChunk008.row8908_mem, Shared.BasisChunk008.row8909_mem, Shared.BasisChunk008.row8910_mem, Shared.BasisChunk008.row8911_mem, Shared.BasisChunk008.row8912_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard116
