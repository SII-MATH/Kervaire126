module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard082
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard082
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard082
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation42_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk001.relation143_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation161_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation171_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk003.relation252_zero, Shared.RelationChunk003.relation255_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation348_zero, Shared.RelationChunk005.relation349_zero, Shared.RelationChunk005.relation350_zero, Shared.RelationChunk005.relation351_zero, Shared.RelationChunk005.relation352_zero, Shared.RelationChunk005.relation353_zero, Shared.RelationChunk005.relation356_zero, Shared.RelationChunk006.relation406_zero, Shared.RelationChunk010.relation525_zero, Shared.RelationChunk010.relation526_zero, Shared.RelationChunk010.relation534_zero, Shared.RelationChunk010.relation535_zero, Shared.RelationChunk010.relation537_zero, Shared.RelationChunk014.relation744_zero, Shared.RelationChunk017.relation846_zero, Shared.RelationChunk017.relation848_zero, Shared.RelationChunk017.relation850_zero, Shared.RelationChunk017.relation851_zero, Shared.RelationChunk017.relation854_zero, Shared.RelationChunk028.relation1174_zero, Shared.RelationChunk028.relation1175_zero, Shared.RelationChunk028.relation1176_zero, Shared.RelationChunk028.relation1177_zero, Shared.RelationChunk028.relation1199_zero, Shared.RelationChunk028.relation1200_zero, Shared.RelationChunk028.relation1202_zero, Shared.RelationChunk028.relation1213_zero, Shared.RelationChunk029.relation1244_zero, Shared.RelationChunk029.relation1245_zero, Shared.RelationChunk029.relation1246_zero, Shared.RelationChunk029.relation1247_zero, Shared.RelationChunk029.relation1249_zero, Shared.RelationChunk029.relation1250_zero, Shared.RelationChunk029.relation1251_zero, Shared.RelationChunk029.relation1256_zero, Shared.RelationChunk029.relation1258_zero, Shared.RelationChunk029.relation1259_zero, Shared.RelationChunk029.relation1260_zero, Shared.RelationChunk029.relation1261_zero, Shared.RelationChunk029.relation1262_zero, Shared.RelationChunk029.relation1263_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10498 128 := by cbv
private def targetRows : List BasisRow := [⟨12, 173, 0, "40,1,324,1"⟩,
  ⟨12, 173, 1, "3,1,712,1"⟩,
  ⟨12, 173, 2, "0,1,790,1"⟩,
  ⟨12, 173, 3, "0,1,789,1"⟩,
  ⟨12, 173, 4, "0,1,2,1,746,1"⟩,
  ⟨11, 173, 0, "2,2,18,1,376,1"⟩,
  ⟨11, 173, 1, "0,1,793,1"⟩,
  ⟨11, 173, 2, "0,1,791,1"⟩,
  ⟨10, 173, 1, "1,1,782,1"⟩,
  ⟨10, 173, 2, "0,3,18,1,446,1"⟩,
  ⟨9, 173, 2, "0,3,34,1,324,1"⟩,
  ⟨8, 173, 0, "0,1,36,1,324,1"⟩,
  ⟨7, 173, 0, "3,1,18,1,378,1"⟩,
  ⟨6, 173, 0, "1,1,4,1,18,1,324,1"⟩,
  ⟨6, 173, 1, "0,1,37,1,324,1"⟩,
  ⟨5, 173, 0, "0,1,38,1,324,1"⟩,
  ⟨174, 174, 0, "0,174"⟩,
  ⟨59, 174, 0, "0,2,783,1"⟩,
  ⟨55, 174, 0, "804,1"⟩,
  ⟨51, 174, 0, "8,1,16,1,296,1"⟩,
  ⟨50, 174, 0, "8,1,17,1,296,1"⟩,
  ⟨49, 174, 0, "8,1,607,1"⟩,
  ⟨48, 174, 0, "8,4,182,1"⟩,
  ⟨48, 174, 1, "0,10,686,1"⟩,
  ⟨47, 174, 0, "8,4,183,1"⟩,
  ⟨47, 174, 1, "0,46,324,1"⟩,
  ⟨46, 174, 1, "8,2,16,1,17,1,111,1"⟩,
  ⟨45, 174, 0, "806,1"⟩,
  ⟨45, 174, 1, "8,3,265,1"⟩,
  ⟨44, 174, 0, "8,6,71,1"⟩,
  ⟨43, 174, 0, "8,5,16,1,50,1"⟩,
  ⟨43, 174, 1, "0,4,17,1,452,1"⟩,
  ⟨42, 174, 1, "8,5,17,1,50,1"⟩,
  ⟨42, 174, 2, "0,3,17,2,225,1"⟩,
  ⟨41, 174, 0, "8,2,433,1"⟩,
  ⟨41, 174, 1, "8,5,125,1"⟩,
  ⟨41, 174, 2, "0,7,725,1"⟩,
  ⟨40, 174, 0, "8,1,17,1,298,1"⟩,
  ⟨40, 174, 1, "8,8,16,1"⟩,
  ⟨40, 174, 2, "0,5,752,1"⟩,
  ⟨39, 174, 0, "17,2,238,1"⟩,
  ⟨39, 174, 1, "8,8,17,1"⟩,
  ⟨38, 174, 0, "8,4,184,1"⟩,
  ⟨38, 174, 1, "8,6,16,1,23,1"⟩,
  ⟨37, 174, 0, "8,4,185,1"⟩,
  ⟨37, 174, 1, "8,7,42,1"⟩,
  ⟨36, 174, 1, "8,3,17,1,147,1"⟩,
  ⟨36, 174, 2, "8,7,13,2"⟩,
  ⟨35, 174, 0, "64,1,225,1"⟩,
  ⟨35, 174, 1, "8,2,17,2,113,1"⟩,
  ⟨35, 174, 2, "8,6,13,1,32,1"⟩,
  ⟨35, 174, 3, "0,1,16,1,491,1"⟩,
  ⟨34, 174, 0, "138,2"⟩,
  ⟨34, 174, 1, "8,5,13,2,23,1"⟩,
  ⟨34, 174, 2, "8,6,72,1"⟩,
  ⟨34, 174, 3, "0,1,17,1,491,1"⟩,
  ⟨33, 174, 0, "809,1"⟩,
  ⟨33, 174, 1, "808,1"⟩,
  ⟨33, 174, 3, "8,4,13,2,51,1"⟩,
  ⟨33, 174, 4, "8,5,127,1"⟩,
  ⟨32, 174, 0, "8,1,16,1,64,2"⟩,
  ⟨32, 174, 1, "8,3,13,5"⟩,
  ⟨32, 174, 2, "8,4,20,1,80,1"⟩,
  ⟨32, 174, 3, "0,1,795,1"⟩,
  ⟨31, 174, 0, "8,1,16,1,299,1"⟩,
  ⟨31, 174, 1, "8,2,13,4,32,1"⟩,
  ⟨31, 174, 2, "8,4,186,1"⟩,
  ⟨31, 174, 3, "0,1,8,3,260,1"⟩,
  ⟨30, 174, 0, "8,1,13,5,23,1"⟩,
  ⟨30, 174, 1, "8,2,434,1"⟩,
  ⟨30, 174, 2, "8,3,9,1,13,1,101,1"⟩,
  ⟨30, 174, 3, "0,1,8,1,16,1,292,1"⟩,
  ⟨29, 174, 0, "13,5,51,1"⟩,
  ⟨29, 174, 1, "8,2,435,1"⟩,
  ⟨29, 174, 2, "8,2,9,1,13,2,80,1"⟩,
  ⟨28, 174, 0, "13,5,52,1"⟩,
  ⟨28, 174, 1, "8,1,9,1,13,1,23,1,101,1"⟩,
  ⟨28, 174, 2, "8,4,187,1"⟩,
  ⟨27, 174, 0, "9,1,13,2,23,1,80,1"⟩,
  ⟨27, 174, 1, "8,4,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6270_mem, Shared.BasisChunk006.row6271_mem, Shared.BasisChunk006.row6272_mem, Shared.BasisChunk006.row6273_mem, Shared.BasisChunk006.row6274_mem, Shared.BasisChunk006.row6275_mem, Shared.BasisChunk006.row6276_mem, Shared.BasisChunk006.row6277_mem, Shared.BasisChunk006.row6279_mem, Shared.BasisChunk006.row6280_mem, Shared.BasisChunk006.row6283_mem, Shared.BasisChunk006.row6284_mem, Shared.BasisChunk006.row6285_mem, Shared.BasisChunk006.row6286_mem, Shared.BasisChunk006.row6287_mem, Shared.BasisChunk006.row6288_mem, Shared.BasisChunk006.row6289_mem, Shared.BasisChunk006.row6290_mem, Shared.BasisChunk006.row6292_mem, Shared.BasisChunk006.row6294_mem, Shared.BasisChunk006.row6295_mem, Shared.BasisChunk006.row6296_mem, Shared.BasisChunk006.row6297_mem, Shared.BasisChunk006.row6298_mem, Shared.BasisChunk006.row6299_mem, Shared.BasisChunk006.row6300_mem, Shared.BasisChunk006.row6302_mem, Shared.BasisChunk006.row6303_mem, Shared.BasisChunk006.row6304_mem, Shared.BasisChunk006.row6305_mem, Shared.BasisChunk006.row6306_mem, Shared.BasisChunk006.row6307_mem, Shared.BasisChunk006.row6309_mem, Shared.BasisChunk006.row6310_mem, Shared.BasisChunk006.row6311_mem, Shared.BasisChunk006.row6312_mem, Shared.BasisChunk006.row6313_mem, Shared.BasisChunk006.row6314_mem, Shared.BasisChunk006.row6315_mem, Shared.BasisChunk006.row6316_mem, Shared.BasisChunk006.row6317_mem, Shared.BasisChunk006.row6318_mem, Shared.BasisChunk006.row6319_mem, Shared.BasisChunk006.row6320_mem, Shared.BasisChunk006.row6321_mem, Shared.BasisChunk006.row6322_mem, Shared.BasisChunk006.row6324_mem, Shared.BasisChunk006.row6325_mem, Shared.BasisChunk006.row6326_mem, Shared.BasisChunk006.row6327_mem, Shared.BasisChunk006.row6328_mem, Shared.BasisChunk006.row6329_mem, Shared.BasisChunk006.row6330_mem, Shared.BasisChunk006.row6331_mem, Shared.BasisChunk006.row6332_mem, Shared.BasisChunk006.row6333_mem, Shared.BasisChunk006.row6334_mem, Shared.BasisChunk006.row6335_mem, Shared.BasisChunk006.row6337_mem, Shared.BasisChunk006.row6338_mem, Shared.BasisChunk006.row6339_mem, Shared.BasisChunk006.row6340_mem, Shared.BasisChunk006.row6341_mem, Shared.BasisChunk006.row6342_mem, Shared.BasisChunk006.row6343_mem, Shared.BasisChunk006.row6344_mem, Shared.BasisChunk006.row6345_mem, Shared.BasisChunk006.row6346_mem, Shared.BasisChunk006.row6347_mem, Shared.BasisChunk006.row6348_mem, Shared.BasisChunk006.row6349_mem, Shared.BasisChunk006.row6350_mem, Shared.BasisChunk006.row6351_mem, Shared.BasisChunk006.row6352_mem, Shared.BasisChunk006.row6353_mem, Shared.BasisChunk006.row6355_mem, Shared.BasisChunk006.row6356_mem, Shared.BasisChunk006.row6357_mem, Shared.BasisChunk006.row6358_mem, Shared.BasisChunk006.row6359_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard082
