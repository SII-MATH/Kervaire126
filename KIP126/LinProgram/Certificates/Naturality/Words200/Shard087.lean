import KIP126.LinProgram.Generated.Naturality.Words200.Shard087
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard087
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard087
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation6_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation26_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation49_zero, Shared.RelationChunk000.relation50_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation161_zero, Shared.RelationChunk001.relation165_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation168_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation175_zero, Shared.RelationChunk001.relation181_zero, Shared.RelationChunk001.relation182_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation230_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation272_zero, Shared.RelationChunk003.relation274_zero, Shared.RelationChunk003.relation275_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation294_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation367_zero, Shared.RelationChunk006.relation368_zero, Shared.RelationChunk006.relation369_zero, Shared.RelationChunk006.relation370_zero, Shared.RelationChunk006.relation371_zero, Shared.RelationChunk006.relation372_zero, Shared.RelationChunk008.relation462_zero, Shared.RelationChunk011.relation572_zero, Shared.RelationChunk011.relation573_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk011.relation579_zero, Shared.RelationChunk011.relation580_zero, Shared.RelationChunk011.relation584_zero, Shared.RelationChunk012.relation622_zero, Shared.RelationChunk016.relation789_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk018.relation858_zero, Shared.RelationChunk018.relation874_zero, Shared.RelationChunk019.relation895_zero, Shared.RelationChunk019.relation896_zero, Shared.RelationChunk019.relation897_zero, Shared.RelationChunk019.relation900_zero, Shared.RelationChunk019.relation901_zero, Shared.RelationChunk028.relation1201_zero, Shared.RelationChunk029.relation1238_zero, Shared.RelationChunk029.relation1251_zero, Shared.RelationChunk030.relation1271_zero, Shared.RelationChunk030.relation1275_zero, Shared.RelationChunk030.relation1276_zero, Shared.RelationChunk031.relation1298_zero, Shared.RelationChunk031.relation1312_zero, Shared.RelationChunk031.relation1321_zero, Shared.RelationChunk032.relation1328_zero, Shared.RelationChunk032.relation1329_zero, Shared.RelationChunk032.relation1330_zero, Shared.RelationChunk032.relation1331_zero, Shared.RelationChunk032.relation1332_zero, Shared.RelationChunk032.relation1333_zero, Shared.RelationChunk032.relation1334_zero, Shared.RelationChunk032.relation1335_zero, Shared.RelationChunk032.relation1336_zero, Shared.RelationChunk032.relation1337_zero, Shared.RelationChunk032.relation1338_zero, Shared.RelationChunk032.relation1339_zero, Shared.RelationChunk032.relation1340_zero, Shared.RelationChunk032.relation1342_zero, Shared.RelationChunk032.relation1343_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11138 128 := by cbv
private def targetRows : List BasisRow := [⟨43, 177, 0, "8,6,78,1"⟩,
  ⟨42, 177, 1, "8,5,17,1,56,1"⟩,
  ⟨41, 177, 0, "8,2,16,1,225,1"⟩,
  ⟨41, 177, 1, "8,5,136,1"⟩,
  ⟨40, 177, 0, "8,2,17,1,225,1"⟩,
  ⟨40, 177, 1, "8,8,19,1"⟩,
  ⟨39, 177, 0, "8,1,42,1,224,1"⟩,
  ⟨39, 177, 1, "8,8,20,1"⟩,
  ⟨39, 177, 2, "0,3,64,1,224,1"⟩,
  ⟨38, 177, 0, "8,5,137,1"⟩,
  ⟨38, 177, 1, "8,7,45,1"⟩,
  ⟨38, 177, 2, "0,3,64,1,225,1"⟩,
  ⟨37, 177, 0, "8,5,138,1"⟩,
  ⟨37, 177, 1, "8,7,46,1"⟩,
  ⟨37, 177, 2, "0,4,17,1,491,1"⟩,
  ⟨36, 177, 1, "8,3,16,1,154,1"⟩,
  ⟨36, 177, 2, "8,6,9,1,13,2"⟩,
  ⟨36, 177, 3, "0,3,809,1"⟩,
  ⟨36, 177, 4, "0,3,807,1"⟩,
  ⟨35, 177, 0, "64,1,238,1"⟩,
  ⟨35, 177, 1, "8,3,17,1,154,1"⟩,
  ⟨35, 177, 2, "8,5,9,1,13,1,32,1"⟩,
  ⟨35, 177, 3, "0,1,8,1,623,1"⟩,
  ⟨35, 177, 4, "0,4,795,1"⟩,
  ⟨34, 177, 0, "8,1,637,1"⟩,
  ⟨34, 177, 1, "8,4,9,1,13,2,23,1"⟩,
  ⟨34, 177, 2, "8,6,79,1"⟩,
  ⟨34, 177, 3, "0,1,17,1,516,1"⟩,
  ⟨33, 177, 0, "17,1,529,1"⟩,
  ⟨33, 177, 1, "8,3,9,1,13,2,51,1"⟩,
  ⟨33, 177, 2, "8,6,80,1"⟩,
  ⟨33, 177, 3, "0,1,830,1"⟩,
  ⟨32, 177, 0, "8,2,64,1,112,1"⟩,
  ⟨32, 177, 1, "8,2,9,1,13,5"⟩,
  ⟨32, 177, 2, "8,4,22,1,80,1"⟩,
  ⟨31, 177, 0, "8,1,9,1,13,4,32,1"⟩,
  ⟨31, 177, 1, "8,2,64,1,113,1"⟩,
  ⟨31, 177, 2, "8,4,23,1,80,1"⟩,
  ⟨30, 177, 0, "9,1,13,5,23,1"⟩,
  ⟨30, 177, 1, "8,2,471,1"⟩,
  ⟨30, 177, 2, "8,3,13,2,101,1"⟩,
  ⟨29, 177, 0, "8,1,9,1,435,1"⟩,
  ⟨29, 177, 1, "8,2,13,3,80,1"⟩,
  ⟨28, 177, 0, "8,1,13,2,23,1,101,1"⟩,
  ⟨28, 177, 1, "8,4,201,1"⟩,
  ⟨27, 177, 0, "13,3,23,1,80,1"⟩,
  ⟨27, 177, 1, "8,3,9,1,188,1"⟩,
  ⟨26, 177, 0, "8,2,9,1,267,1"⟩,
  ⟨25, 177, 1, "8,1,9,1,23,1,188,1"⟩,
  ⟨25, 177, 2, "0,1,8,1,627,1"⟩,
  ⟨24, 177, 0, "855,1"⟩,
  ⟨24, 177, 1, "854,1"⟩,
  ⟨24, 177, 2, "9,1,13,2,212,1"⟩,
  ⟨24, 177, 3, "0,1,832,1"⟩,
  ⟨23, 177, 1, "13,2,328,1"⟩,
  ⟨23, 177, 2, "8,1,638,1"⟩,
  ⟨22, 177, 0, "13,1,581,1"⟩,
  ⟨22, 177, 1, "8,1,640,1"⟩,
  ⟨21, 177, 0, "80,1,212,1"⟩,
  ⟨20, 177, 1, "8,1,17,1,333,1"⟩,
  ⟨20, 177, 2, "0,1,64,1,235,1"⟩,
  ⟨20, 177, 3, "0,9,743,1"⟩,
  ⟨19, 177, 1, "13,2,331,1"⟩,
  ⟨19, 177, 2, "0,1,837,1"⟩,
  ⟨19, 177, 3, "0,1,836,1"⟩,
  ⟨19, 177, 4, "0,1,835,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6665_mem, Shared.BasisChunk006.row6667_mem, Shared.BasisChunk006.row6668_mem, Shared.BasisChunk006.row6669_mem, Shared.BasisChunk006.row6670_mem, Shared.BasisChunk006.row6671_mem, Shared.BasisChunk006.row6672_mem, Shared.BasisChunk006.row6673_mem, Shared.BasisChunk006.row6674_mem, Shared.BasisChunk006.row6675_mem, Shared.BasisChunk006.row6676_mem, Shared.BasisChunk006.row6677_mem, Shared.BasisChunk006.row6678_mem, Shared.BasisChunk006.row6679_mem, Shared.BasisChunk006.row6680_mem, Shared.BasisChunk006.row6682_mem, Shared.BasisChunk006.row6683_mem, Shared.BasisChunk006.row6684_mem, Shared.BasisChunk006.row6685_mem, Shared.BasisChunk006.row6686_mem, Shared.BasisChunk006.row6687_mem, Shared.BasisChunk006.row6688_mem, Shared.BasisChunk006.row6689_mem, Shared.BasisChunk006.row6690_mem, Shared.BasisChunk006.row6691_mem, Shared.BasisChunk006.row6692_mem, Shared.BasisChunk006.row6693_mem, Shared.BasisChunk006.row6694_mem, Shared.BasisChunk006.row6695_mem, Shared.BasisChunk006.row6696_mem, Shared.BasisChunk006.row6697_mem, Shared.BasisChunk006.row6698_mem, Shared.BasisChunk006.row6699_mem, Shared.BasisChunk006.row6700_mem, Shared.BasisChunk006.row6701_mem, Shared.BasisChunk006.row6702_mem, Shared.BasisChunk006.row6703_mem, Shared.BasisChunk006.row6704_mem, Shared.BasisChunk006.row6705_mem, Shared.BasisChunk006.row6706_mem, Shared.BasisChunk006.row6707_mem, Shared.BasisChunk006.row6708_mem, Shared.BasisChunk006.row6709_mem, Shared.BasisChunk006.row6710_mem, Shared.BasisChunk006.row6711_mem, Shared.BasisChunk006.row6712_mem, Shared.BasisChunk006.row6713_mem, Shared.BasisChunk006.row6714_mem, Shared.BasisChunk006.row6716_mem, Shared.BasisChunk006.row6717_mem, Shared.BasisChunk006.row6718_mem, Shared.BasisChunk006.row6719_mem, Shared.BasisChunk006.row6720_mem, Shared.BasisChunk006.row6721_mem, Shared.BasisChunk006.row6723_mem, Shared.BasisChunk006.row6724_mem, Shared.BasisChunk006.row6725_mem, Shared.BasisChunk006.row6726_mem, Shared.BasisChunk006.row6727_mem, Shared.BasisChunk006.row6730_mem, Shared.BasisChunk006.row6731_mem, Shared.BasisChunk006.row6732_mem, Shared.BasisChunk006.row6734_mem, Shared.BasisChunk006.row6735_mem, Shared.BasisChunk006.row6736_mem, Shared.BasisChunk006.row6737_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard087
