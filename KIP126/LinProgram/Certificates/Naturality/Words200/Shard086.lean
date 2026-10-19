module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard086
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard086
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard086
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk006.relation377_zero, Shared.RelationChunk006.relation378_zero, Shared.RelationChunk006.relation379_zero, Shared.RelationChunk007.relation413_zero, Shared.RelationChunk010.relation546_zero, Shared.RelationChunk011.relation585_zero, Shared.RelationChunk011.relation586_zero, Shared.RelationChunk011.relation587_zero, Shared.RelationChunk015.relation778_zero, Shared.RelationChunk017.relation812_zero, Shared.RelationChunk018.relation865_zero, Shared.RelationChunk018.relation866_zero, Shared.RelationChunk018.relation867_zero, Shared.RelationChunk018.relation868_zero, Shared.RelationChunk018.relation869_zero, Shared.RelationChunk018.relation870_zero, Shared.RelationChunk018.relation871_zero, Shared.RelationChunk019.relation904_zero, Shared.RelationChunk019.relation905_zero, Shared.RelationChunk029.relation1229_zero, Shared.RelationChunk029.relation1230_zero, Shared.RelationChunk029.relation1231_zero, Shared.RelationChunk030.relation1270_zero, Shared.RelationChunk030.relation1285_zero, Shared.RelationChunk030.relation1286_zero, Shared.RelationChunk030.relation1287_zero, Shared.RelationChunk030.relation1288_zero, Shared.RelationChunk030.relation1289_zero, Shared.RelationChunk030.relation1290_zero, Shared.RelationChunk030.relation1291_zero, Shared.RelationChunk030.relation1292_zero, Shared.RelationChunk030.relation1293_zero, Shared.RelationChunk030.relation1294_zero, Shared.RelationChunk030.relation1295_zero, Shared.RelationChunk030.relation1296_zero, Shared.RelationChunk031.relation1301_zero, Shared.RelationChunk031.relation1302_zero, Shared.RelationChunk031.relation1303_zero, Shared.RelationChunk031.relation1304_zero, Shared.RelationChunk031.relation1305_zero, Shared.RelationChunk031.relation1306_zero, Shared.RelationChunk031.relation1307_zero, Shared.RelationChunk031.relation1308_zero, Shared.RelationChunk031.relation1309_zero, Shared.RelationChunk032.relation1344_zero, Shared.RelationChunk032.relation1345_zero, Shared.RelationChunk032.relation1346_zero, Shared.RelationChunk032.relation1347_zero, Shared.RelationChunk032.relation1348_zero, Shared.RelationChunk032.relation1349_zero, Shared.RelationChunk032.relation1350_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11010 128 := by cbv
private def targetRows : List BasisRow := [⟨28, 176, 1, "8,1,20,1,292,1"⟩,
  ⟨28, 176, 2, "8,2,455,1"⟩,
  ⟨27, 176, 0, "13,2,23,1,150,1"⟩,
  ⟨27, 176, 1, "8,1,625,1"⟩,
  ⟨27, 176, 2, "8,1,9,1,420,1"⟩,
  ⟨27, 176, 3, "0,3,797,1"⟩,
  ⟨26, 176, 0, "9,1,13,1,346,1"⟩,
  ⟨26, 176, 1, "8,3,279,1"⟩,
  ⟨26, 176, 2, "0,2,811,1"⟩,
  ⟨26, 176, 3, "0,6,64,1,209,1"⟩,
  ⟨25, 176, 0, "8,3,280,1"⟩,
  ⟨25, 176, 1, "0,6,760,1"⟩,
  ⟨24, 176, 1, "8,2,9,1,261,1"⟩,
  ⟨23, 176, 1, "8,1,9,1,423,1"⟩,
  ⟨23, 176, 2, "0,6,762,1"⟩,
  ⟨22, 176, 0, "9,1,13,2,209,1"⟩,
  ⟨22, 176, 1, "0,2,8,1,613,1"⟩,
  ⟨21, 176, 1, "833,1"⟩,
  ⟨19, 176, 0, "80,1,209,1"⟩,
  ⟨19, 176, 2, "0,8,743,1"⟩,
  ⟨18, 176, 0, "837,1"⟩,
  ⟨18, 176, 2, "835,1"⟩,
  ⟨18, 176, 3, "3,2,648,1"⟩,
  ⟨17, 176, 0, "839,1"⟩,
  ⟨17, 176, 2, "0,1,107,1,174,1"⟩,
  ⟨17, 176, 3, "0,3,18,1,475,1"⟩,
  ⟨16, 176, 1, "0,1,825,1"⟩,
  ⟨16, 176, 2, "0,1,824,1"⟩,
  ⟨16, 176, 3, "0,2,814,1"⟩,
  ⟨16, 176, 4, "0,3,39,1,324,1"⟩,
  ⟨15, 176, 1, "0,1,3,1,731,1"⟩,
  ⟨15, 176, 2, "0,1,3,1,730,1"⟩,
  ⟨15, 176, 3, "0,2,815,1"⟩,
  ⟨14, 176, 0, "844,1"⟩,
  ⟨14, 176, 4, "0,2,817,1"⟩,
  ⟨14, 176, 5, "0,2,3,1,719,1"⟩,
  ⟨13, 176, 0, "845,1"⟩,
  ⟨13, 176, 2, "1,1,3,1,719,1"⟩,
  ⟨13, 176, 3, "0,1,826,1"⟩,
  ⟨13, 176, 4, "0,1,3,1,734,1"⟩,
  ⟨12, 176, 0, "8,1,17,1,324,1"⟩,
  ⟨12, 176, 1, "1,1,7,1,632,1"⟩,
  ⟨12, 176, 2, "0,2,818,1"⟩,
  ⟨11, 176, 0, "7,1,68,1,163,1"⟩,
  ⟨11, 176, 2, "0,1,828,1"⟩,
  ⟨10, 176, 0, "846,1"⟩,
  ⟨9, 176, 1, "13,2,324,1"⟩,
  ⟨8, 176, 0, "848,1"⟩,
  ⟨7, 176, 0, "6,1,18,1,324,1"⟩,
  ⟨7, 176, 1, "3,1,749,1"⟩,
  ⟨5, 176, 1, "3,1,751,1"⟩,
  ⟨4, 176, 1, "3,2,18,1,324,1"⟩,
  ⟨177, 177, 0, "0,177"⟩,
  ⟨58, 177, 0, "0,3,804,1"⟩,
  ⟨55, 177, 0, "852,1"⟩,
  ⟨51, 177, 0, "8,2,470,1"⟩,
  ⟨51, 177, 1, "0,13,686,1"⟩,
  ⟨50, 177, 0, "8,1,17,1,326,1"⟩,
  ⟨50, 177, 1, "0,49,324,1"⟩,
  ⟨49, 177, 0, "8,1,634,1"⟩,
  ⟨49, 177, 1, "0,3,805,1"⟩,
  ⟨48, 177, 0, "8,4,199,1"⟩,
  ⟨47, 177, 0, "8,4,200,1"⟩,
  ⟨46, 177, 1, "8,3,17,1,153,1"⟩,
  ⟨45, 177, 0, "8,1,636,1"⟩,
  ⟨45, 177, 1, "8,3,283,1"⟩,
  ⟨44, 177, 0, "8,6,77,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6571_mem, Shared.BasisChunk006.row6572_mem, Shared.BasisChunk006.row6573_mem, Shared.BasisChunk006.row6574_mem, Shared.BasisChunk006.row6575_mem, Shared.BasisChunk006.row6576_mem, Shared.BasisChunk006.row6577_mem, Shared.BasisChunk006.row6578_mem, Shared.BasisChunk006.row6579_mem, Shared.BasisChunk006.row6580_mem, Shared.BasisChunk006.row6581_mem, Shared.BasisChunk006.row6582_mem, Shared.BasisChunk006.row6584_mem, Shared.BasisChunk006.row6586_mem, Shared.BasisChunk006.row6587_mem, Shared.BasisChunk006.row6588_mem, Shared.BasisChunk006.row6589_mem, Shared.BasisChunk006.row6591_mem, Shared.BasisChunk006.row6593_mem, Shared.BasisChunk006.row6595_mem, Shared.BasisChunk006.row6596_mem, Shared.BasisChunk006.row6598_mem, Shared.BasisChunk006.row6599_mem, Shared.BasisChunk006.row6600_mem, Shared.BasisChunk006.row6602_mem, Shared.BasisChunk006.row6603_mem, Shared.BasisChunk006.row6605_mem, Shared.BasisChunk006.row6606_mem, Shared.BasisChunk006.row6607_mem, Shared.BasisChunk006.row6608_mem, Shared.BasisChunk006.row6610_mem, Shared.BasisChunk006.row6611_mem, Shared.BasisChunk006.row6612_mem, Shared.BasisChunk006.row6613_mem, Shared.BasisChunk006.row6617_mem, Shared.BasisChunk006.row6618_mem, Shared.BasisChunk006.row6619_mem, Shared.BasisChunk006.row6621_mem, Shared.BasisChunk006.row6622_mem, Shared.BasisChunk006.row6623_mem, Shared.BasisChunk006.row6624_mem, Shared.BasisChunk006.row6625_mem, Shared.BasisChunk006.row6626_mem, Shared.BasisChunk006.row6627_mem, Shared.BasisChunk006.row6629_mem, Shared.BasisChunk006.row6630_mem, Shared.BasisChunk006.row6634_mem, Shared.BasisChunk006.row6636_mem, Shared.BasisChunk006.row6638_mem, Shared.BasisChunk006.row6639_mem, Shared.BasisChunk006.row6643_mem, Shared.BasisChunk006.row6645_mem, Shared.BasisChunk006.row6647_mem, Shared.BasisChunk006.row6648_mem, Shared.BasisChunk006.row6650_mem, Shared.BasisChunk006.row6652_mem, Shared.BasisChunk006.row6653_mem, Shared.BasisChunk006.row6654_mem, Shared.BasisChunk006.row6655_mem, Shared.BasisChunk006.row6656_mem, Shared.BasisChunk006.row6657_mem, Shared.BasisChunk006.row6658_mem, Shared.BasisChunk006.row6659_mem, Shared.BasisChunk006.row6661_mem, Shared.BasisChunk006.row6662_mem, Shared.BasisChunk006.row6663_mem, Shared.BasisChunk006.row6664_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard086
