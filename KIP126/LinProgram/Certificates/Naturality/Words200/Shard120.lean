import KIP126.LinProgram.Generated.Naturality.Words200.Shard120
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk051
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk053
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk054
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard120
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard120
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation42_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation103_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk010.relation550_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk011.relation607_zero, Shared.RelationChunk011.relation608_zero, Shared.RelationChunk011.relation609_zero, Shared.RelationChunk011.relation610_zero, Shared.RelationChunk011.relation612_zero, Shared.RelationChunk011.relation613_zero, Shared.RelationChunk011.relation614_zero, Shared.RelationChunk011.relation615_zero, Shared.RelationChunk011.relation616_zero, Shared.RelationChunk011.relation617_zero, Shared.RelationChunk014.relation718_zero, Shared.RelationChunk015.relation780_zero, Shared.RelationChunk020.relation925_zero, Shared.RelationChunk020.relation926_zero, Shared.RelationChunk020.relation927_zero, Shared.RelationChunk020.relation928_zero, Shared.RelationChunk020.relation929_zero, Shared.RelationChunk034.relation1385_zero, Shared.RelationChunk034.relation1387_zero, Shared.RelationChunk034.relation1388_zero, Shared.RelationChunk034.relation1393_zero, Shared.RelationChunk034.relation1394_zero, Shared.RelationChunk051.relation1814_zero, Shared.RelationChunk051.relation1815_zero, Shared.RelationChunk051.relation1816_zero, Shared.RelationChunk053.relation1857_zero, Shared.RelationChunk053.relation1858_zero, Shared.RelationChunk053.relation1859_zero, Shared.RelationChunk053.relation1860_zero, Shared.RelationChunk053.relation1861_zero, Shared.RelationChunk053.relation1862_zero, Shared.RelationChunk053.relation1863_zero, Shared.RelationChunk053.relation1864_zero, Shared.RelationChunk053.relation1865_zero, Shared.RelationChunk053.relation1866_zero, Shared.RelationChunk053.relation1867_zero, Shared.RelationChunk053.relation1868_zero, Shared.RelationChunk053.relation1869_zero, Shared.RelationChunk053.relation1870_zero, Shared.RelationChunk053.relation1871_zero, Shared.RelationChunk053.relation1872_zero, Shared.RelationChunk053.relation1873_zero, Shared.RelationChunk053.relation1874_zero, Shared.RelationChunk053.relation1875_zero, Shared.RelationChunk053.relation1876_zero, Shared.RelationChunk054.relation1878_zero, Shared.RelationChunk054.relation1879_zero, Shared.RelationChunk054.relation1880_zero, Shared.RelationChunk054.relation1881_zero, Shared.RelationChunk054.relation1882_zero, Shared.RelationChunk054.relation1883_zero, Shared.RelationChunk054.relation1884_zero, Shared.RelationChunk054.relation1885_zero, Shared.RelationChunk054.relation1886_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15362 128 := by cbv
private def targetRows : List BasisRow := [⟨16, 196, 2, "2,2,990,1"⟩,
  ⟨16, 196, 5, "0,1,67,1,352,1"⟩,
  ⟨16, 196, 6, "0,5,64,1,324,1"⟩,
  ⟨15, 196, 0, "43,1,543,1"⟩,
  ⟨15, 196, 1, "3,1,990,1"⟩,
  ⟨15, 196, 2, "2,1,1055,1"⟩,
  ⟨15, 196, 5, "0,1,1098,1"⟩,
  ⟨15, 196, 6, "0,2,1091,1"⟩,
  ⟨15, 196, 7, "0,4,66,1,324,1"⟩,
  ⟨14, 196, 0, "1115,1"⟩,
  ⟨14, 196, 1, "1114,1"⟩,
  ⟨14, 196, 2, "43,1,544,1"⟩,
  ⟨14, 196, 3, "2,1,1057,1"⟩,
  ⟨14, 196, 4, "0,1,1099,1"⟩,
  ⟨13, 196, 0, "1117,1"⟩,
  ⟨13, 196, 1, "1116,1"⟩,
  ⟨13, 196, 2, "0,2,72,1,324,1"⟩,
  ⟨12, 196, 0, "1119,1"⟩,
  ⟨12, 196, 2, "1,1,72,1,324,1"⟩,
  ⟨9, 196, 0, "0,1,73,1,324,1"⟩,
  ⟨8, 196, 0, "0,1,75,1,324,1"⟩,
  ⟨8, 196, 1, "0,1,74,1,324,1"⟩,
  ⟨8, 196, 2, "0,4,1058,1"⟩,
  ⟨7, 196, 0, "18,1,24,1,324,1"⟩,
  ⟨7, 196, 1, "0,4,18,2,324,1"⟩,
  ⟨5, 196, 0, "2,1,1058,1"⟩,
  ⟨4, 196, 0, "2,1,18,2,324,1"⟩,
  ⟨197, 197, 0, "0,197"⟩,
  ⟨66, 197, 0, "0,1,1101,1"⟩,
  ⟨62, 197, 0, "0,2,8,1,851,1"⟩,
  ⟨61, 197, 0, "0,2,8,1,852,1"⟩,
  ⟨52, 197, 0, "0,2,8,2,635,1"⟩,
  ⟨51, 197, 0, "0,2,8,2,636,1"⟩,
  ⟨50, 197, 0, "0,3,17,1,685,1"⟩,
  ⟨49, 197, 0, "0,2,17,2,403,1"⟩,
  ⟨48, 197, 2, "0,6,1033,1"⟩,
  ⟨47, 197, 0, "17,1,722,1"⟩,
  ⟨47, 197, 1, "0,4,1059,1"⟩,
  ⟨46, 197, 0, "8,1,872,1"⟩,
  ⟨45, 197, 0, "8,1,873,1"⟩,
  ⟨45, 197, 1, "0,3,1076,1"⟩,
  ⟨44, 197, 0, "8,3,488,1"⟩,
  ⟨43, 197, 0, "8,2,17,1,343,1"⟩,
  ⟨42, 197, 1, "8,3,489,1"⟩,
  ⟨41, 197, 0, "17,1,725,1"⟩,
  ⟨41, 197, 1, "8,3,490,1"⟩,
  ⟨41, 197, 2, "0,14,919,1"⟩,
  ⟨40, 197, 0, "8,5,206,1"⟩,
  ⟨39, 197, 1, "8,4,17,1,160,1"⟩,
  ⟨38, 197, 0, "8,1,64,1,244,1"⟩,
  ⟨38, 197, 1, "8,3,491,1"⟩,
  ⟨38, 197, 2, "8,5,207,1"⟩,
  ⟨37, 197, 0, "8,1,138,1,149,1"⟩,
  ⟨37, 197, 1, "8,1,16,1,17,1,260,1"⟩,
  ⟨37, 197, 2, "8,5,208,1"⟩,
  ⟨36, 197, 0, "8,1,64,1,245,1"⟩,
  ⟨36, 197, 1, "8,1,17,2,260,1"⟩,
  ⟨36, 197, 2, "8,4,9,1,194,1"⟩,
  ⟨35, 197, 0, "8,1,60,1,260,1"⟩,
  ⟨35, 197, 1, "8,2,653,1"⟩,
  ⟨35, 197, 2, "8,3,9,1,13,1,167,1"⟩,
  ⟨34, 197, 0, "8,2,16,1,347,1"⟩,
  ⟨34, 197, 1, "8,2,9,1,13,1,248,1"⟩,
  ⟨34, 197, 2, "8,4,291,1"⟩,
  ⟨33, 197, 0, "8,1,9,1,13,2,219,1"⟩,
  ⟨33, 197, 1, "8,2,17,1,347,1"⟩,
  ⟨33, 197, 2, "8,4,292,1"⟩,
  ⟨32, 197, 1, "9,1,13,3,194,1"⟩,
  ⟨32, 197, 2, "8,2,22,1,292,1"⟩,
  ⟨32, 197, 3, "8,3,492,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row9093_mem, Shared.BasisChunk008.row9096_mem, Shared.BasisChunk008.row9097_mem, Shared.BasisChunk008.row9098_mem, Shared.BasisChunk008.row9099_mem, Shared.BasisChunk008.row9100_mem, Shared.BasisChunk008.row9103_mem, Shared.BasisChunk008.row9104_mem, Shared.BasisChunk008.row9105_mem, Shared.BasisChunk008.row9106_mem, Shared.BasisChunk008.row9107_mem, Shared.BasisChunk008.row9108_mem, Shared.BasisChunk008.row9109_mem, Shared.BasisChunk008.row9110_mem, Shared.BasisChunk008.row9111_mem, Shared.BasisChunk008.row9112_mem, Shared.BasisChunk008.row9113_mem, Shared.BasisChunk008.row9114_mem, Shared.BasisChunk008.row9116_mem, Shared.BasisChunk008.row9118_mem, Shared.BasisChunk008.row9119_mem, Shared.BasisChunk008.row9120_mem, Shared.BasisChunk008.row9121_mem, Shared.BasisChunk008.row9122_mem, Shared.BasisChunk008.row9123_mem, Shared.BasisChunk008.row9125_mem, Shared.BasisChunk008.row9127_mem, Shared.BasisChunk008.row9128_mem, Shared.BasisChunk008.row9129_mem, Shared.BasisChunk008.row9130_mem, Shared.BasisChunk008.row9131_mem, Shared.BasisChunk008.row9133_mem, Shared.BasisChunk008.row9134_mem, Shared.BasisChunk008.row9135_mem, Shared.BasisChunk008.row9136_mem, Shared.BasisChunk008.row9139_mem, Shared.BasisChunk008.row9140_mem, Shared.BasisChunk008.row9141_mem, Shared.BasisChunk008.row9142_mem, Shared.BasisChunk008.row9143_mem, Shared.BasisChunk008.row9144_mem, Shared.BasisChunk008.row9145_mem, Shared.BasisChunk008.row9146_mem, Shared.BasisChunk008.row9148_mem, Shared.BasisChunk008.row9149_mem, Shared.BasisChunk008.row9150_mem, Shared.BasisChunk008.row9151_mem, Shared.BasisChunk008.row9152_mem, Shared.BasisChunk008.row9154_mem, Shared.BasisChunk008.row9155_mem, Shared.BasisChunk008.row9156_mem, Shared.BasisChunk008.row9157_mem, Shared.BasisChunk008.row9158_mem, Shared.BasisChunk008.row9159_mem, Shared.BasisChunk008.row9160_mem, Shared.BasisChunk008.row9161_mem, Shared.BasisChunk008.row9162_mem, Shared.BasisChunk008.row9163_mem, Shared.BasisChunk008.row9164_mem, Shared.BasisChunk008.row9165_mem, Shared.BasisChunk008.row9166_mem, Shared.BasisChunk008.row9167_mem, Shared.BasisChunk008.row9168_mem, Shared.BasisChunk008.row9169_mem, Shared.BasisChunk008.row9170_mem, Shared.BasisChunk008.row9171_mem, Shared.BasisChunk008.row9172_mem, Shared.BasisChunk008.row9174_mem, Shared.BasisChunk008.row9175_mem, Shared.BasisChunk008.row9176_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard120
