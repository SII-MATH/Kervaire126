module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard122
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk053
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk054
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk055
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk009

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard122
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard122
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation39_zero, Shared.RelationChunk000.relation40_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation110_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation161_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk003.relation278_zero, Shared.RelationChunk003.relation279_zero, Shared.RelationChunk003.relation280_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation284_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk006.relation395_zero, Shared.RelationChunk006.relation396_zero, Shared.RelationChunk006.relation397_zero, Shared.RelationChunk006.relation400_zero, Shared.RelationChunk006.relation405_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk009.relation493_zero, Shared.RelationChunk012.relation630_zero, Shared.RelationChunk012.relation634_zero, Shared.RelationChunk012.relation635_zero, Shared.RelationChunk012.relation638_zero, Shared.RelationChunk014.relation738_zero, Shared.RelationChunk021.relation949_zero, Shared.RelationChunk021.relation950_zero, Shared.RelationChunk021.relation951_zero, Shared.RelationChunk021.relation952_zero, Shared.RelationChunk021.relation954_zero, Shared.RelationChunk021.relation955_zero, Shared.RelationChunk021.relation956_zero, Shared.RelationChunk025.relation1071_zero, Shared.RelationChunk029.relation1257_zero, Shared.RelationChunk035.relation1431_zero, Shared.RelationChunk035.relation1433_zero, Shared.RelationChunk035.relation1435_zero, Shared.RelationChunk035.relation1437_zero, Shared.RelationChunk035.relation1439_zero, Shared.RelationChunk053.relation1877_zero, Shared.RelationChunk054.relation1887_zero, Shared.RelationChunk055.relation1916_zero, Shared.RelationChunk055.relation1917_zero, Shared.RelationChunk055.relation1918_zero, Shared.RelationChunk055.relation1919_zero, Shared.RelationChunk055.relation1920_zero, Shared.RelationChunk055.relation1921_zero, Shared.RelationChunk055.relation1922_zero, Shared.RelationChunk055.relation1923_zero, Shared.RelationChunk055.relation1924_zero, Shared.RelationChunk055.relation1925_zero, Shared.RelationChunk055.relation1926_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15618 128 := by cbv
private def targetRows : List BasisRow := [⟨13, 197, 0, "1135,1"⟩,
  ⟨13, 197, 1, "9,1,13,2,324,1"⟩,
  ⟨13, 197, 2, "0,1,1118,1"⟩,
  ⟨12, 197, 0, "1136,1"⟩,
  ⟨12, 197, 1, "0,1,1120,1"⟩,
  ⟨11, 197, 0, "1138,1"⟩,
  ⟨11, 197, 2, "79,1,324,1"⟩,
  ⟨10, 197, 0, "80,1,324,1"⟩,
  ⟨10, 197, 1, "1,1,18,1,684,1"⟩,
  ⟨10, 197, 2, "0,2,73,1,324,1"⟩,
  ⟨9, 197, 0, "0,2,74,1,324,1"⟩,
  ⟨9, 197, 1, "0,5,1058,1"⟩,
  ⟨8, 197, 1, "0,5,18,2,324,1"⟩,
  ⟨7, 197, 0, "2,1,18,1,660,1"⟩,
  ⟨7, 197, 1, "1,1,76,1,324,1"⟩,
  ⟨6, 197, 0, "2,1,70,1,324,1"⟩,
  ⟨6, 197, 1, "0,1,2,1,1058,1"⟩,
  ⟨5, 197, 0, "0,1,2,1,18,2,324,1"⟩,
  ⟨198, 198, 0, "0,198"⟩,
  ⟨67, 198, 0, "0,2,1101,1"⟩,
  ⟨63, 198, 0, "1140,1"⟩,
  ⟨59, 198, 0, "8,1,16,1,554,1"⟩,
  ⟨58, 198, 0, "8,1,17,1,554,1"⟩,
  ⟨57, 198, 0, "8,1,886,1"⟩,
  ⟨56, 198, 0, "8,4,295,1"⟩,
  ⟨55, 198, 0, "8,4,296,1"⟩,
  ⟨54, 198, 1, "8,2,16,1,17,1,183,1"⟩,
  ⟨53, 198, 0, "1142,1"⟩,
  ⟨53, 198, 1, "8,3,498,1"⟩,
  ⟨52, 198, 0, "8,6,145,1"⟩,
  ⟨51, 198, 0, "8,5,16,1,111,1"⟩,
  ⟨51, 198, 1, "0,4,17,1,685,1"⟩,
  ⟨50, 198, 1, "8,5,17,1,111,1"⟩,
  ⟨50, 198, 2, "0,3,17,2,403,1"⟩,
  ⟨49, 198, 0, "8,2,663,1"⟩,
  ⟨49, 198, 1, "8,5,211,1"⟩,
  ⟨49, 198, 2, "0,7,1033,1"⟩,
  ⟨48, 198, 0, "8,1,17,1,556,1"⟩,
  ⟨48, 198, 1, "8,8,49,1"⟩,
  ⟨48, 198, 2, "0,5,1059,1"⟩,
  ⟨47, 198, 0, "17,2,433,1"⟩,
  ⟨47, 198, 1, "8,8,50,1"⟩,
  ⟨46, 198, 0, "8,4,297,1"⟩,
  ⟨46, 198, 1, "8,6,16,1,17,2"⟩,
  ⟨45, 198, 0, "8,4,298,1"⟩,
  ⟨45, 198, 1, "8,7,88,1"⟩,
  ⟨44, 198, 1, "8,3,17,1,238,1"⟩,
  ⟨44, 198, 2, "8,11"⟩,
  ⟨43, 198, 0, "64,1,403,1"⟩,
  ⟨43, 198, 1, "8,2,17,2,185,1"⟩,
  ⟨43, 198, 2, "8,9,22,1"⟩,
  ⟨43, 198, 3, "0,1,16,1,725,1"⟩,
  ⟨42, 198, 0, "138,1,225,1"⟩,
  ⟨42, 198, 1, "8,6,146,1"⟩,
  ⟨42, 198, 2, "8,9,23,1"⟩,
  ⟨42, 198, 3, "0,1,17,1,725,1"⟩,
  ⟨41, 198, 0, "1144,1"⟩,
  ⟨41, 198, 2, "8,6,147,1"⟩,
  ⟨41, 198, 3, "8,8,51,1"⟩,
  ⟨40, 198, 0, "8,1,16,1,64,1,137,1"⟩,
  ⟨40, 198, 1, "8,5,17,1,113,1"⟩,
  ⟨40, 198, 2, "8,7,13,3"⟩,
  ⟨39, 198, 0, "8,1,16,1,64,1,138,1"⟩,
  ⟨39, 198, 1, "8,4,17,1,162,1"⟩,
  ⟨39, 198, 2, "8,6,13,2,32,1"⟩,
  ⟨39, 198, 3, "0,1,8,3,491,1"⟩,
  ⟨38, 198, 0, "8,2,664,1"⟩,
  ⟨38, 198, 1, "8,5,13,3,23,1"⟩,
  ⟨38, 198, 2, "8,7,89,1"⟩,
  ⟨38, 198, 3, "0,1,8,1,16,1,17,1,260,1"⟩,
  ⟨37, 198, 0, "8,2,665,1"⟩,
  ⟨37, 198, 1, "8,4,13,3,51,1"⟩,
  ⟨37, 198, 2, "8,6,9,1,80,1"⟩,
  ⟨36, 198, 0, "8,3,13,6"⟩,
  ⟨36, 198, 1, "8,4,64,2"⟩,
  ⟨36, 198, 2, "8,5,23,1,89,1"⟩,
  ⟨35, 198, 0, "8,2,13,5,32,1"⟩,
  ⟨35, 198, 1, "8,4,299,1"⟩,
  ⟨35, 198, 2, "8,4,9,1,23,1,80,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk009.row9261_mem, Shared.BasisChunk009.row9262_mem, Shared.BasisChunk009.row9263_mem, Shared.BasisChunk009.row9264_mem, Shared.BasisChunk009.row9265_mem, Shared.BasisChunk009.row9266_mem, Shared.BasisChunk009.row9268_mem, Shared.BasisChunk009.row9269_mem, Shared.BasisChunk009.row9270_mem, Shared.BasisChunk009.row9271_mem, Shared.BasisChunk009.row9272_mem, Shared.BasisChunk009.row9273_mem, Shared.BasisChunk009.row9275_mem, Shared.BasisChunk009.row9276_mem, Shared.BasisChunk009.row9277_mem, Shared.BasisChunk009.row9278_mem, Shared.BasisChunk009.row9279_mem, Shared.BasisChunk009.row9280_mem, Shared.BasisChunk009.row9281_mem, Shared.BasisChunk009.row9282_mem, Shared.BasisChunk009.row9284_mem, Shared.BasisChunk009.row9286_mem, Shared.BasisChunk009.row9287_mem, Shared.BasisChunk009.row9288_mem, Shared.BasisChunk009.row9289_mem, Shared.BasisChunk009.row9290_mem, Shared.BasisChunk009.row9292_mem, Shared.BasisChunk009.row9293_mem, Shared.BasisChunk009.row9294_mem, Shared.BasisChunk009.row9295_mem, Shared.BasisChunk009.row9296_mem, Shared.BasisChunk009.row9297_mem, Shared.BasisChunk009.row9299_mem, Shared.BasisChunk009.row9300_mem, Shared.BasisChunk009.row9301_mem, Shared.BasisChunk009.row9302_mem, Shared.BasisChunk009.row9303_mem, Shared.BasisChunk009.row9304_mem, Shared.BasisChunk009.row9305_mem, Shared.BasisChunk009.row9306_mem, Shared.BasisChunk009.row9307_mem, Shared.BasisChunk009.row9308_mem, Shared.BasisChunk009.row9309_mem, Shared.BasisChunk009.row9310_mem, Shared.BasisChunk009.row9311_mem, Shared.BasisChunk009.row9312_mem, Shared.BasisChunk009.row9314_mem, Shared.BasisChunk009.row9315_mem, Shared.BasisChunk009.row9316_mem, Shared.BasisChunk009.row9317_mem, Shared.BasisChunk009.row9318_mem, Shared.BasisChunk009.row9319_mem, Shared.BasisChunk009.row9320_mem, Shared.BasisChunk009.row9321_mem, Shared.BasisChunk009.row9322_mem, Shared.BasisChunk009.row9323_mem, Shared.BasisChunk009.row9324_mem, Shared.BasisChunk009.row9326_mem, Shared.BasisChunk009.row9327_mem, Shared.BasisChunk009.row9328_mem, Shared.BasisChunk009.row9329_mem, Shared.BasisChunk009.row9330_mem, Shared.BasisChunk009.row9331_mem, Shared.BasisChunk009.row9332_mem, Shared.BasisChunk009.row9333_mem, Shared.BasisChunk009.row9334_mem, Shared.BasisChunk009.row9335_mem, Shared.BasisChunk009.row9336_mem, Shared.BasisChunk009.row9337_mem, Shared.BasisChunk009.row9338_mem, Shared.BasisChunk009.row9339_mem, Shared.BasisChunk009.row9340_mem, Shared.BasisChunk009.row9341_mem, Shared.BasisChunk009.row9343_mem, Shared.BasisChunk009.row9344_mem, Shared.BasisChunk009.row9345_mem, Shared.BasisChunk009.row9346_mem, Shared.BasisChunk009.row9347_mem, Shared.BasisChunk009.row9348_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard122
