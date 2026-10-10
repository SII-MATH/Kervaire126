import KIP126.LinProgram.Generated.Naturality.Words200.Shard095
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk036
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk037
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard095
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard095
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation17_zero, Shared.RelationChunk000.relation60_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk005.relation344_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk007.relation417_zero, Shared.RelationChunk008.relation471_zero, Shared.RelationChunk008.relation472_zero, Shared.RelationChunk008.relation481_zero, Shared.RelationChunk010.relation550_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk012.relation660_zero, Shared.RelationChunk012.relation661_zero, Shared.RelationChunk012.relation662_zero, Shared.RelationChunk013.relation665_zero, Shared.RelationChunk013.relation666_zero, Shared.RelationChunk013.relation667_zero, Shared.RelationChunk013.relation668_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk013.relation673_zero, Shared.RelationChunk013.relation675_zero, Shared.RelationChunk015.relation785_zero, Shared.RelationChunk018.relation868_zero, Shared.RelationChunk018.relation875_zero, Shared.RelationChunk020.relation918_zero, Shared.RelationChunk022.relation970_zero, Shared.RelationChunk022.relation971_zero, Shared.RelationChunk022.relation972_zero, Shared.RelationChunk022.relation973_zero, Shared.RelationChunk022.relation974_zero, Shared.RelationChunk022.relation975_zero, Shared.RelationChunk022.relation976_zero, Shared.RelationChunk022.relation977_zero, Shared.RelationChunk036.relation1462_zero, Shared.RelationChunk036.relation1463_zero, Shared.RelationChunk036.relation1464_zero, Shared.RelationChunk036.relation1465_zero, Shared.RelationChunk036.relation1466_zero, Shared.RelationChunk036.relation1467_zero, Shared.RelationChunk036.relation1468_zero, Shared.RelationChunk036.relation1469_zero, Shared.RelationChunk036.relation1470_zero, Shared.RelationChunk036.relation1471_zero, Shared.RelationChunk036.relation1472_zero, Shared.RelationChunk036.relation1473_zero, Shared.RelationChunk036.relation1474_zero, Shared.RelationChunk036.relation1475_zero, Shared.RelationChunk037.relation1480_zero, Shared.RelationChunk037.relation1481_zero, Shared.RelationChunk037.relation1482_zero, Shared.RelationChunk037.relation1483_zero, Shared.RelationChunk037.relation1484_zero, Shared.RelationChunk037.relation1485_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12162 128 := by cbv
private def targetRows : List BasisRow := [⟨7, 181, 1, "0,1,2,1,43,1,324,1"⟩,
  ⟨6, 181, 1, "0,1,2,1,849,1"⟩,
  ⟨5, 181, 0, "0,1,2,1,850,1"⟩,
  ⟨182, 182, 0, "0,182"⟩,
  ⟨58, 182, 0, "0,2,8,1,661,1"⟩,
  ⟨57, 182, 0, "0,2,16,1,554,1"⟩,
  ⟨56, 182, 0, "0,2,17,1,554,1"⟩,
  ⟨55, 182, 0, "0,54,324,1"⟩,
  ⟨48, 182, 0, "0,2,8,1,662,1"⟩,
  ⟨47, 182, 0, "0,2,8,1,663,1"⟩,
  ⟨47, 182, 1, "0,3,871,1"⟩,
  ⟨43, 182, 0, "0,8,64,1,225,1"⟩,
  ⟨42, 182, 0, "8,1,686,1"⟩,
  ⟨41, 182, 0, "8,1,687,1"⟩,
  ⟨41, 182, 1, "0,8,807,1"⟩,
  ⟨40, 182, 0, "8,2,16,1,244,1"⟩,
  ⟨40, 182, 1, "0,9,795,1"⟩,
  ⟨39, 182, 0, "8,2,17,1,244,1"⟩,
  ⟨38, 182, 1, "8,2,16,1,245,1"⟩,
  ⟨37, 182, 0, "8,3,315,1"⟩,
  ⟨37, 182, 1, "0,2,16,1,64,1,138,1"⟩,
  ⟨37, 182, 2, "0,3,64,1,244,1"⟩,
  ⟨36, 182, 0, "8,5,149,1"⟩,
  ⟨36, 182, 1, "0,3,138,1,149,1"⟩,
  ⟨35, 182, 0, "8,3,16,1,167,1"⟩,
  ⟨35, 182, 1, "0,3,17,2,260,1"⟩,
  ⟨34, 182, 2, "8,4,218,1"⟩,
  ⟨34, 182, 3, "0,3,64,1,246,1"⟩,
  ⟨34, 182, 4, "0,3,59,1,260,1"⟩,
  ⟨33, 182, 0, "138,1,160,1"⟩,
  ⟨33, 182, 1, "8,1,17,1,380,1"⟩,
  ⟨33, 182, 2, "8,4,219,1"⟩,
  ⟨33, 182, 3, "0,4,862,1"⟩,
  ⟨32, 182, 0, "17,2,278,1"⟩,
  ⟨32, 182, 1, "8,1,688,1"⟩,
  ⟨32, 182, 2, "8,3,13,1,194,1"⟩,
  ⟨31, 182, 0, "42,1,380,1"⟩,
  ⟨31, 182, 1, "8,1,689,1"⟩,
  ⟨31, 182, 2, "8,2,13,2,167,1"⟩,
  ⟨31, 182, 3, "0,1,889,1"⟩,
  ⟨30, 182, 0, "8,1,13,2,248,1"⟩,
  ⟨30, 182, 1, "8,2,517,1"⟩,
  ⟨30, 182, 2, "8,3,316,1"⟩,
  ⟨29, 182, 0, "13,3,219,1"⟩,
  ⟨29, 182, 1, "8,2,518,1"⟩,
  ⟨29, 182, 2, "8,2,9,1,292,1"⟩,
  ⟨28, 182, 1, "13,3,220,1"⟩,
  ⟨28, 182, 2, "8,1,23,1,316,1"⟩,
  ⟨28, 182, 3, "8,3,318,1"⟩,
  ⟨27, 182, 0, "897,1"⟩,
  ⟨27, 182, 1, "9,1,23,1,292,1"⟩,
  ⟨27, 182, 2, "8,2,9,1,293,1"⟩,
  ⟨26, 182, 0, "8,3,9,1,209,1"⟩,
  ⟨25, 182, 1, "8,2,9,1,294,1"⟩,
  ⟨25, 182, 2, "0,14,743,1"⟩,
  ⟨24, 182, 0, "900,1"⟩,
  ⟨24, 182, 2, "8,1,690,1"⟩,
  ⟨24, 182, 3, "8,1,9,1,13,1,261,1"⟩,
  ⟨24, 182, 4, "0,6,836,1"⟩,
  ⟨23, 182, 2, "901,1"⟩,
  ⟨23, 182, 3, "9,1,13,1,423,1"⟩,
  ⟨22, 182, 0, "64,1,261,1"⟩,
  ⟨21, 182, 0, "904,1"⟩,
  ⟨21, 182, 1, "8,1,692,1"⟩,
  ⟨20, 182, 0, "101,1,209,1"⟩,
  ⟨20, 182, 1, "13,1,629,1"⟩,
  ⟨20, 182, 2, "0,2,47,1,324,1"⟩,
  ⟨19, 182, 0, "905,1"⟩,
  ⟨18, 182, 0, "2,1,866,1"⟩,
  ⟨18, 182, 1, "0,1,891,1"⟩,
  ⟨17, 182, 0, "908,1"⟩,
  ⟨17, 182, 1, "907,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7240_mem, Shared.BasisChunk007.row7242_mem, Shared.BasisChunk007.row7243_mem, Shared.BasisChunk007.row7244_mem, Shared.BasisChunk007.row7246_mem, Shared.BasisChunk007.row7247_mem, Shared.BasisChunk007.row7248_mem, Shared.BasisChunk007.row7249_mem, Shared.BasisChunk007.row7251_mem, Shared.BasisChunk007.row7252_mem, Shared.BasisChunk007.row7253_mem, Shared.BasisChunk007.row7255_mem, Shared.BasisChunk007.row7256_mem, Shared.BasisChunk007.row7257_mem, Shared.BasisChunk007.row7258_mem, Shared.BasisChunk007.row7259_mem, Shared.BasisChunk007.row7260_mem, Shared.BasisChunk007.row7261_mem, Shared.BasisChunk007.row7263_mem, Shared.BasisChunk007.row7264_mem, Shared.BasisChunk007.row7265_mem, Shared.BasisChunk007.row7266_mem, Shared.BasisChunk007.row7267_mem, Shared.BasisChunk007.row7268_mem, Shared.BasisChunk007.row7269_mem, Shared.BasisChunk007.row7270_mem, Shared.BasisChunk007.row7273_mem, Shared.BasisChunk007.row7274_mem, Shared.BasisChunk007.row7275_mem, Shared.BasisChunk007.row7276_mem, Shared.BasisChunk007.row7277_mem, Shared.BasisChunk007.row7278_mem, Shared.BasisChunk007.row7279_mem, Shared.BasisChunk007.row7280_mem, Shared.BasisChunk007.row7281_mem, Shared.BasisChunk007.row7282_mem, Shared.BasisChunk007.row7283_mem, Shared.BasisChunk007.row7284_mem, Shared.BasisChunk007.row7285_mem, Shared.BasisChunk007.row7286_mem, Shared.BasisChunk007.row7287_mem, Shared.BasisChunk007.row7288_mem, Shared.BasisChunk007.row7289_mem, Shared.BasisChunk007.row7290_mem, Shared.BasisChunk007.row7291_mem, Shared.BasisChunk007.row7292_mem, Shared.BasisChunk007.row7294_mem, Shared.BasisChunk007.row7295_mem, Shared.BasisChunk007.row7296_mem, Shared.BasisChunk007.row7297_mem, Shared.BasisChunk007.row7298_mem, Shared.BasisChunk007.row7299_mem, Shared.BasisChunk007.row7300_mem, Shared.BasisChunk007.row7302_mem, Shared.BasisChunk007.row7303_mem, Shared.BasisChunk007.row7304_mem, Shared.BasisChunk007.row7306_mem, Shared.BasisChunk007.row7307_mem, Shared.BasisChunk007.row7308_mem, Shared.BasisChunk007.row7311_mem, Shared.BasisChunk007.row7312_mem, Shared.BasisChunk007.row7313_mem, Shared.BasisChunk007.row7315_mem, Shared.BasisChunk007.row7316_mem, Shared.BasisChunk007.row7317_mem, Shared.BasisChunk007.row7318_mem, Shared.BasisChunk007.row7319_mem, Shared.BasisChunk007.row7320_mem, Shared.BasisChunk007.row7321_mem, Shared.BasisChunk007.row7322_mem, Shared.BasisChunk007.row7323_mem, Shared.BasisChunk007.row7324_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard095
