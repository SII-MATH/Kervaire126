import KIP126.LinProgram.Generated.Naturality.Words200.Shard101
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk039
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk040
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk041
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard101
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard101
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation26_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation82_zero, Shared.RelationChunk000.relation83_zero, Shared.RelationChunk000.relation84_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation90_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation110_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation168_zero, Shared.RelationChunk001.relation169_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation193_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk001.relation198_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk001.relation207_zero, Shared.RelationChunk001.relation208_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation232_zero, Shared.RelationChunk003.relation260_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation306_zero, Shared.RelationChunk004.relation307_zero, Shared.RelationChunk004.relation308_zero, Shared.RelationChunk004.relation315_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation371_zero, Shared.RelationChunk006.relation376_zero, Shared.RelationChunk007.relation420_zero, Shared.RelationChunk007.relation421_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk008.relation452_zero, Shared.RelationChunk008.relation453_zero, Shared.RelationChunk008.relation455_zero, Shared.RelationChunk008.relation458_zero, Shared.RelationChunk010.relation537_zero, Shared.RelationChunk014.relation738_zero, Shared.RelationChunk014.relation739_zero, Shared.RelationChunk014.relation740_zero, Shared.RelationChunk014.relation741_zero, Shared.RelationChunk014.relation742_zero, Shared.RelationChunk014.relation744_zero, Shared.RelationChunk014.relation745_zero, Shared.RelationChunk014.relation750_zero, Shared.RelationChunk017.relation846_zero, Shared.RelationChunk021.relation954_zero, Shared.RelationChunk024.relation1045_zero, Shared.RelationChunk024.relation1046_zero, Shared.RelationChunk024.relation1047_zero, Shared.RelationChunk024.relation1048_zero, Shared.RelationChunk025.relation1068_zero, Shared.RelationChunk025.relation1069_zero, Shared.RelationChunk025.relation1070_zero, Shared.RelationChunk025.relation1076_zero, Shared.RelationChunk025.relation1078_zero, Shared.RelationChunk025.relation1081_zero, Shared.RelationChunk025.relation1082_zero, Shared.RelationChunk025.relation1085_zero, Shared.RelationChunk025.relation1086_zero, Shared.RelationChunk025.relation1087_zero, Shared.RelationChunk025.relation1090_zero, Shared.RelationChunk039.relation1550_zero, Shared.RelationChunk039.relation1551_zero, Shared.RelationChunk039.relation1552_zero, Shared.RelationChunk039.relation1554_zero, Shared.RelationChunk039.relation1555_zero, Shared.RelationChunk039.relation1556_zero, Shared.RelationChunk039.relation1557_zero, Shared.RelationChunk039.relation1558_zero, Shared.RelationChunk039.relation1559_zero, Shared.RelationChunk039.relation1560_zero, Shared.RelationChunk040.relation1569_zero, Shared.RelationChunk040.relation1570_zero, Shared.RelationChunk041.relation1602_zero, Shared.RelationChunk041.relation1603_zero, Shared.RelationChunk041.relation1604_zero, Shared.RelationChunk041.relation1605_zero, Shared.RelationChunk041.relation1606_zero, Shared.RelationChunk041.relation1607_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12930 128 := by cbv
private def targetRows : List BasisRow := [⟨11, 185, 2, "0,1,3,1,847,1"⟩,
  ⟨10, 185, 0, "1,1,12,1,18,1,324,1"⟩,
  ⟨10, 185, 1, "0,2,53,1,324,1"⟩,
  ⟨8, 185, 0, "2,1,894,1"⟩,
  ⟨7, 185, 0, "0,1,3,1,43,1,324,1"⟩,
  ⟨6, 185, 0, "57,1,324,1"⟩,
  ⟨186, 186, 0, "0,186"⟩,
  ⟨63, 186, 0, "0,2,926,1"⟩,
  ⟨59, 186, 0, "0,58,324,1"⟩,
  ⟨55, 186, 0, "8,2,554,1"⟩,
  ⟨54, 186, 0, "16,1,17,1,296,1"⟩,
  ⟨53, 186, 0, "8,1,736,1"⟩,
  ⟨53, 186, 1, "0,3,916,1"⟩,
  ⟨52, 186, 0, "8,4,236,1"⟩,
  ⟨52, 186, 1, "0,3,917,1"⟩,
  ⟨51, 186, 0, "8,3,16,1,183,1"⟩,
  ⟨50, 186, 1, "8,3,17,1,183,1"⟩,
  ⟨49, 186, 0, "953,1"⟩,
  ⟨49, 186, 1, "8,3,354,1"⟩,
  ⟨48, 186, 0, "8,6,110,1"⟩,
  ⟨47, 186, 0, "8,6,111,1"⟩,
  ⟨46, 186, 1, "8,4,16,1,17,1,50,1"⟩,
  ⟨45, 186, 0, "8,2,556,1"⟩,
  ⟨45, 186, 1, "8,5,161,1"⟩,
  ⟨45, 186, 2, "0,12,807,1"⟩,
  ⟨44, 186, 0, "8,1,17,1,433,1"⟩,
  ⟨44, 186, 1, "8,8,31,1"⟩,
  ⟨44, 186, 2, "0,13,795,1"⟩,
  ⟨43, 186, 0, "17,2,298,1"⟩,
  ⟨43, 186, 1, "8,7,16,1,17,1"⟩,
  ⟨42, 186, 0, "8,4,237,1"⟩,
  ⟨42, 186, 1, "8,7,17,2"⟩,
  ⟨41, 186, 0, "8,4,238,1"⟩,
  ⟨41, 186, 1, "8,7,60,1"⟩,
  ⟨40, 186, 0, "8,3,17,1,185,1"⟩,
  ⟨40, 186, 1, "8,9,13,1"⟩,
  ⟨39, 186, 0, "8,2,17,2,147,1"⟩,
  ⟨39, 186, 1, "8,8,32,1"⟩,
  ⟨39, 186, 2, "0,1,8,1,725,1"⟩,
  ⟨38, 186, 0, "954,1"⟩,
  ⟨38, 186, 1, "8,6,112,1"⟩,
  ⟨38, 186, 2, "8,7,13,1,23,1"⟩,
  ⟨37, 186, 1, "8,6,113,1"⟩,
  ⟨37, 186, 2, "8,6,13,1,51,1"⟩,
  ⟨36, 186, 0, "8,2,64,1,137,1"⟩,
  ⟨36, 186, 1, "8,5,162,1"⟩,
  ⟨36, 186, 2, "8,5,13,4"⟩,
  ⟨35, 186, 0, "8,2,64,1,138,1"⟩,
  ⟨35, 186, 1, "8,4,23,1,113,1"⟩,
  ⟨35, 186, 2, "8,4,13,3,32,1"⟩,
  ⟨35, 186, 3, "0,1,8,2,16,1,260,1"⟩,
  ⟨34, 186, 0, "8,2,557,1"⟩,
  ⟨34, 186, 1, "8,3,13,4,23,1"⟩,
  ⟨34, 186, 2, "8,5,9,1,101,1"⟩,
  ⟨34, 186, 3, "0,1,8,2,17,1,260,1"⟩,
  ⟨34, 186, 4, "0,2,149,2"⟩,
  ⟨33, 186, 0, "8,2,559,1"⟩,
  ⟨33, 186, 1, "8,2,13,4,51,1"⟩,
  ⟨33, 186, 2, "8,4,9,1,13,1,80,1"⟩,
  ⟨33, 186, 4, "0,2,927,1"⟩,
  ⟨32, 186, 0, "8,1,13,7"⟩,
  ⟨32, 186, 1, "8,3,16,1,187,1"⟩,
  ⟨32, 186, 2, "8,3,9,1,23,1,101,1"⟩,
  ⟨32, 186, 3, "0,4,64,1,260,1"⟩,
  ⟨31, 186, 0, "13,6,32,1"⟩,
  ⟨31, 186, 1, "8,2,9,1,13,1,23,1,80,1"⟩,
  ⟨31, 186, 2, "8,3,16,1,188,1"⟩,
  ⟨31, 186, 3, "0,2,64,1,274,1"⟩,
  ⟨31, 186, 4, "0,4,897,1"⟩,
  ⟨30, 186, 0, "13,6,33,1"⟩,
  ⟨30, 186, 1, "8,1,9,1,13,3,101,1"⟩,
  ⟨30, 186, 2, "8,3,17,1,188,1"⟩,
  ⟨30, 186, 4, "0,3,921,1"⟩,
  ⟨30, 186, 5, "0,3,919,1"⟩,
  ⟨29, 186, 0, "9,1,13,4,80,1"⟩,
  ⟨29, 186, 1, "8,2,17,1,267,1"⟩,
  ⟨29, 186, 2, "0,1,64,1,278,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7719_mem, Shared.BasisChunk007.row7720_mem, Shared.BasisChunk007.row7721_mem, Shared.BasisChunk007.row7723_mem, Shared.BasisChunk007.row7724_mem, Shared.BasisChunk007.row7725_mem, Shared.BasisChunk007.row7726_mem, Shared.BasisChunk007.row7727_mem, Shared.BasisChunk007.row7729_mem, Shared.BasisChunk007.row7731_mem, Shared.BasisChunk007.row7732_mem, Shared.BasisChunk007.row7733_mem, Shared.BasisChunk007.row7734_mem, Shared.BasisChunk007.row7735_mem, Shared.BasisChunk007.row7736_mem, Shared.BasisChunk007.row7737_mem, Shared.BasisChunk007.row7739_mem, Shared.BasisChunk007.row7740_mem, Shared.BasisChunk007.row7741_mem, Shared.BasisChunk007.row7742_mem, Shared.BasisChunk007.row7743_mem, Shared.BasisChunk007.row7745_mem, Shared.BasisChunk007.row7746_mem, Shared.BasisChunk007.row7747_mem, Shared.BasisChunk007.row7748_mem, Shared.BasisChunk007.row7749_mem, Shared.BasisChunk007.row7750_mem, Shared.BasisChunk007.row7751_mem, Shared.BasisChunk007.row7752_mem, Shared.BasisChunk007.row7753_mem, Shared.BasisChunk007.row7754_mem, Shared.BasisChunk007.row7755_mem, Shared.BasisChunk007.row7756_mem, Shared.BasisChunk007.row7757_mem, Shared.BasisChunk007.row7758_mem, Shared.BasisChunk007.row7759_mem, Shared.BasisChunk007.row7760_mem, Shared.BasisChunk007.row7761_mem, Shared.BasisChunk007.row7762_mem, Shared.BasisChunk007.row7763_mem, Shared.BasisChunk007.row7764_mem, Shared.BasisChunk007.row7765_mem, Shared.BasisChunk007.row7767_mem, Shared.BasisChunk007.row7768_mem, Shared.BasisChunk007.row7769_mem, Shared.BasisChunk007.row7770_mem, Shared.BasisChunk007.row7771_mem, Shared.BasisChunk007.row7772_mem, Shared.BasisChunk007.row7773_mem, Shared.BasisChunk007.row7774_mem, Shared.BasisChunk007.row7775_mem, Shared.BasisChunk007.row7776_mem, Shared.BasisChunk007.row7777_mem, Shared.BasisChunk007.row7778_mem, Shared.BasisChunk007.row7779_mem, Shared.BasisChunk007.row7780_mem, Shared.BasisChunk007.row7781_mem, Shared.BasisChunk007.row7782_mem, Shared.BasisChunk007.row7783_mem, Shared.BasisChunk007.row7785_mem, Shared.BasisChunk007.row7786_mem, Shared.BasisChunk007.row7787_mem, Shared.BasisChunk007.row7788_mem, Shared.BasisChunk007.row7789_mem, Shared.BasisChunk007.row7790_mem, Shared.BasisChunk007.row7791_mem, Shared.BasisChunk007.row7792_mem, Shared.BasisChunk007.row7793_mem, Shared.BasisChunk007.row7794_mem, Shared.BasisChunk007.row7795_mem, Shared.BasisChunk007.row7796_mem, Shared.BasisChunk007.row7797_mem, Shared.BasisChunk007.row7799_mem, Shared.BasisChunk007.row7800_mem, Shared.BasisChunk007.row7801_mem, Shared.BasisChunk007.row7802_mem, Shared.BasisChunk007.row7803_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard101
