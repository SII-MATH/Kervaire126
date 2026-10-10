import KIP126.LinProgram.Generated.Naturality.Words200.Shard111
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
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk047
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk048
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard111
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard111
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation42_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation63_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation102_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation125_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation171_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk003.relation252_zero, Shared.RelationChunk003.relation255_zero, Shared.RelationChunk003.relation273_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation348_zero, Shared.RelationChunk005.relation349_zero, Shared.RelationChunk005.relation350_zero, Shared.RelationChunk005.relation351_zero, Shared.RelationChunk005.relation352_zero, Shared.RelationChunk005.relation353_zero, Shared.RelationChunk005.relation356_zero, Shared.RelationChunk006.relation406_zero, Shared.RelationChunk007.relation420_zero, Shared.RelationChunk007.relation426_zero, Shared.RelationChunk010.relation525_zero, Shared.RelationChunk010.relation526_zero, Shared.RelationChunk010.relation535_zero, Shared.RelationChunk010.relation537_zero, Shared.RelationChunk012.relation626_zero, Shared.RelationChunk014.relation736_zero, Shared.RelationChunk017.relation834_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk017.relation841_zero, Shared.RelationChunk017.relation842_zero, Shared.RelationChunk017.relation843_zero, Shared.RelationChunk017.relation846_zero, Shared.RelationChunk017.relation848_zero, Shared.RelationChunk017.relation850_zero, Shared.RelationChunk017.relation851_zero, Shared.RelationChunk017.relation853_zero, Shared.RelationChunk024.relation1067_zero, Shared.RelationChunk028.relation1199_zero, Shared.RelationChunk028.relation1200_zero, Shared.RelationChunk028.relation1202_zero, Shared.RelationChunk028.relation1213_zero, Shared.RelationChunk029.relation1244_zero, Shared.RelationChunk029.relation1245_zero, Shared.RelationChunk029.relation1246_zero, Shared.RelationChunk029.relation1247_zero, Shared.RelationChunk029.relation1249_zero, Shared.RelationChunk029.relation1252_zero, Shared.RelationChunk029.relation1253_zero, Shared.RelationChunk029.relation1254_zero, Shared.RelationChunk029.relation1255_zero, Shared.RelationChunk029.relation1256_zero, Shared.RelationChunk047.relation1727_zero, Shared.RelationChunk047.relation1728_zero, Shared.RelationChunk047.relation1729_zero, Shared.RelationChunk047.relation1730_zero, Shared.RelationChunk047.relation1731_zero, Shared.RelationChunk047.relation1732_zero, Shared.RelationChunk047.relation1733_zero, Shared.RelationChunk047.relation1735_zero, Shared.RelationChunk047.relation1736_zero, Shared.RelationChunk047.relation1737_zero, Shared.RelationChunk047.relation1738_zero, Shared.RelationChunk047.relation1739_zero, Shared.RelationChunk047.relation1740_zero, Shared.RelationChunk047.relation1741_zero, Shared.RelationChunk047.relation1742_zero, Shared.RelationChunk047.relation1743_zero, Shared.RelationChunk047.relation1744_zero, Shared.RelationChunk047.relation1745_zero, Shared.RelationChunk047.relation1746_zero, Shared.RelationChunk047.relation1747_zero, Shared.RelationChunk047.relation1748_zero, Shared.RelationChunk047.relation1749_zero, Shared.RelationChunk047.relation1750_zero, Shared.RelationChunk047.relation1751_zero, Shared.RelationChunk048.relation1752_zero, Shared.RelationChunk048.relation1753_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14210 128 := by cbv
private def targetRows : List BasisRow := [⟨52, 192, 1, "0,4,969,1"⟩,
  ⟨51, 192, 0, "8,5,183,1"⟩,
  ⟨51, 192, 1, "0,3,17,1,636,1"⟩,
  ⟨50, 192, 1, "8,3,16,1,17,1,111,1"⟩,
  ⟨49, 192, 0, "8,1,806,1"⟩,
  ⟨49, 192, 1, "8,4,265,1"⟩,
  ⟨49, 192, 2, "0,1,1030,1"⟩,
  ⟨48, 192, 0, "17,1,663,1"⟩,
  ⟨48, 192, 1, "8,7,71,1"⟩,
  ⟨47, 192, 0, "8,6,16,1,50,1"⟩,
  ⟨47, 192, 1, "0,1,1031,1"⟩,
  ⟨46, 192, 0, "8,3,432,1"⟩,
  ⟨46, 192, 1, "8,6,17,1,50,1"⟩,
  ⟨45, 192, 0, "8,3,433,1"⟩,
  ⟨45, 192, 1, "8,6,125,1"⟩,
  ⟨44, 192, 0, "8,2,17,1,298,1"⟩,
  ⟨44, 192, 1, "8,9,16,1"⟩,
  ⟨43, 192, 0, "8,1,17,2,238,1"⟩,
  ⟨43, 192, 1, "8,9,17,1"⟩,
  ⟨43, 192, 2, "0,1,1033,1"⟩,
  ⟨42, 192, 0, "8,5,184,1"⟩,
  ⟨42, 192, 1, "8,7,16,1,23,1"⟩,
  ⟨41, 192, 0, "8,5,185,1"⟩,
  ⟨41, 192, 1, "8,8,42,1"⟩,
  ⟨40, 192, 1, "8,4,17,1,147,1"⟩,
  ⟨40, 192, 2, "8,8,13,2"⟩,
  ⟨39, 192, 0, "8,1,64,1,225,1"⟩,
  ⟨39, 192, 1, "8,3,17,2,113,1"⟩,
  ⟨39, 192, 2, "8,7,13,1,32,1"⟩,
  ⟨39, 192, 3, "0,1,8,1,16,1,491,1"⟩,
  ⟨38, 192, 0, "8,1,138,2"⟩,
  ⟨38, 192, 1, "8,6,13,2,23,1"⟩,
  ⟨38, 192, 2, "8,7,72,1"⟩,
  ⟨38, 192, 3, "0,1,8,1,17,1,491,1"⟩,
  ⟨37, 192, 0, "8,1,808,1"⟩,
  ⟨37, 192, 1, "8,5,13,2,51,1"⟩,
  ⟨37, 192, 2, "8,6,127,1"⟩,
  ⟨36, 192, 0, "8,2,16,1,64,2"⟩,
  ⟨36, 192, 1, "8,4,13,5"⟩,
  ⟨36, 192, 2, "8,5,20,1,80,1"⟩,
  ⟨36, 192, 3, "0,9,919,1"⟩,
  ⟨35, 192, 0, "8,2,16,1,299,1"⟩,
  ⟨35, 192, 1, "8,3,13,4,32,1"⟩,
  ⟨35, 192, 2, "8,5,186,1"⟩,
  ⟨35, 192, 3, "0,10,898,1"⟩,
  ⟨34, 192, 0, "8,2,13,5,23,1"⟩,
  ⟨34, 192, 1, "8,3,434,1"⟩,
  ⟨34, 192, 2, "8,4,9,1,13,1,101,1"⟩,
  ⟨33, 192, 0, "8,1,13,5,51,1"⟩,
  ⟨33, 192, 1, "8,3,435,1"⟩,
  ⟨33, 192, 2, "8,3,9,1,13,2,80,1"⟩,
  ⟨33, 192, 3, "0,3,64,3"⟩,
  ⟨32, 192, 0, "13,8"⟩,
  ⟨32, 192, 1, "8,2,9,1,13,1,23,1,101,1"⟩,
  ⟨32, 192, 2, "8,5,187,1"⟩,
  ⟨32, 192, 3, "0,3,64,1,299,1"⟩,
  ⟨31, 192, 0, "13,5,23,1,24,1"⟩,
  ⟨31, 192, 1, "8,1,9,1,13,2,23,1,80,1"⟩,
  ⟨31, 192, 2, "8,5,188,1"⟩,
  ⟨31, 192, 3, "0,5,963,1"⟩,
  ⟨30, 192, 1, "9,1,13,4,101,1"⟩,
  ⟨30, 192, 2, "8,4,267,1"⟩,
  ⟨30, 192, 3, "0,3,64,1,301,1"⟩,
  ⟨30, 192, 4, "0,4,974,1"⟩,
  ⟨29, 192, 0, "64,1,327,1"⟩,
  ⟨29, 192, 1, "8,3,23,1,188,1"⟩,
  ⟨29, 192, 2, "0,1,8,1,797,1"⟩,
  ⟨29, 192, 3, "0,4,976,1"⟩,
  ⟨28, 192, 0, "8,1,812,1"⟩,
  ⟨28, 192, 1, "8,2,13,2,212,1"⟩,
  ⟨28, 192, 2, "0,1,17,1,655,1"⟩,
  ⟨28, 192, 3, "0,1,2,1,963,1"⟩,
  ⟨28, 192, 4, "0,4,978,1"⟩,
  ⟨27, 192, 0, "13,3,266,1"⟩,
  ⟨27, 192, 2, "8,1,13,3,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8456_mem, Shared.BasisChunk008.row8457_mem, Shared.BasisChunk008.row8458_mem, Shared.BasisChunk008.row8460_mem, Shared.BasisChunk008.row8462_mem, Shared.BasisChunk008.row8463_mem, Shared.BasisChunk008.row8464_mem, Shared.BasisChunk008.row8465_mem, Shared.BasisChunk008.row8466_mem, Shared.BasisChunk008.row8467_mem, Shared.BasisChunk008.row8468_mem, Shared.BasisChunk008.row8469_mem, Shared.BasisChunk008.row8470_mem, Shared.BasisChunk008.row8471_mem, Shared.BasisChunk008.row8472_mem, Shared.BasisChunk008.row8473_mem, Shared.BasisChunk008.row8474_mem, Shared.BasisChunk008.row8475_mem, Shared.BasisChunk008.row8476_mem, Shared.BasisChunk008.row8477_mem, Shared.BasisChunk008.row8478_mem, Shared.BasisChunk008.row8479_mem, Shared.BasisChunk008.row8480_mem, Shared.BasisChunk008.row8481_mem, Shared.BasisChunk008.row8483_mem, Shared.BasisChunk008.row8484_mem, Shared.BasisChunk008.row8485_mem, Shared.BasisChunk008.row8486_mem, Shared.BasisChunk008.row8487_mem, Shared.BasisChunk008.row8488_mem, Shared.BasisChunk008.row8489_mem, Shared.BasisChunk008.row8490_mem, Shared.BasisChunk008.row8491_mem, Shared.BasisChunk008.row8492_mem, Shared.BasisChunk008.row8493_mem, Shared.BasisChunk008.row8494_mem, Shared.BasisChunk008.row8495_mem, Shared.BasisChunk008.row8496_mem, Shared.BasisChunk008.row8497_mem, Shared.BasisChunk008.row8498_mem, Shared.BasisChunk008.row8499_mem, Shared.BasisChunk008.row8500_mem, Shared.BasisChunk008.row8501_mem, Shared.BasisChunk008.row8502_mem, Shared.BasisChunk008.row8503_mem, Shared.BasisChunk008.row8504_mem, Shared.BasisChunk008.row8505_mem, Shared.BasisChunk008.row8506_mem, Shared.BasisChunk008.row8508_mem, Shared.BasisChunk008.row8509_mem, Shared.BasisChunk008.row8510_mem, Shared.BasisChunk008.row8511_mem, Shared.BasisChunk008.row8512_mem, Shared.BasisChunk008.row8513_mem, Shared.BasisChunk008.row8514_mem, Shared.BasisChunk008.row8515_mem, Shared.BasisChunk008.row8516_mem, Shared.BasisChunk008.row8517_mem, Shared.BasisChunk008.row8518_mem, Shared.BasisChunk008.row8519_mem, Shared.BasisChunk008.row8521_mem, Shared.BasisChunk008.row8522_mem, Shared.BasisChunk008.row8523_mem, Shared.BasisChunk008.row8524_mem, Shared.BasisChunk008.row8525_mem, Shared.BasisChunk008.row8526_mem, Shared.BasisChunk008.row8527_mem, Shared.BasisChunk008.row8528_mem, Shared.BasisChunk008.row8529_mem, Shared.BasisChunk008.row8530_mem, Shared.BasisChunk008.row8531_mem, Shared.BasisChunk008.row8532_mem, Shared.BasisChunk008.row8533_mem, Shared.BasisChunk008.row8534_mem, Shared.BasisChunk008.row8536_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard111
