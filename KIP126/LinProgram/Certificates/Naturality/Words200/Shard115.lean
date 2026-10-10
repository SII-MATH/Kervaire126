import KIP126.LinProgram.Generated.Naturality.Words200.Shard115
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk044
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk046
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk047
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk049
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk050
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard115
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard115
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
  exact ⟨Shared.RelationChunk000.relation8_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation48_zero, Shared.RelationChunk000.relation49_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk006.relation391_zero, Shared.RelationChunk007.relation409_zero, Shared.RelationChunk007.relation413_zero, Shared.RelationChunk008.relation445_zero, Shared.RelationChunk010.relation546_zero, Shared.RelationChunk010.relation550_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk013.relation664_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk013.relation670_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk018.relation865_zero, Shared.RelationChunk018.relation866_zero, Shared.RelationChunk018.relation867_zero, Shared.RelationChunk018.relation868_zero, Shared.RelationChunk018.relation869_zero, Shared.RelationChunk018.relation870_zero, Shared.RelationChunk018.relation871_zero, Shared.RelationChunk018.relation872_zero, Shared.RelationChunk018.relation875_zero, Shared.RelationChunk026.relation1113_zero, Shared.RelationChunk026.relation1125_zero, Shared.RelationChunk028.relation1180_zero, Shared.RelationChunk031.relation1299_zero, Shared.RelationChunk031.relation1300_zero, Shared.RelationChunk031.relation1301_zero, Shared.RelationChunk031.relation1303_zero, Shared.RelationChunk031.relation1307_zero, Shared.RelationChunk031.relation1308_zero, Shared.RelationChunk031.relation1309_zero, Shared.RelationChunk031.relation1310_zero, Shared.RelationChunk031.relation1311_zero, Shared.RelationChunk031.relation1312_zero, Shared.RelationChunk044.relation1688_zero, Shared.RelationChunk046.relation1700_zero, Shared.RelationChunk047.relation1734_zero, Shared.RelationChunk049.relation1765_zero, Shared.RelationChunk049.relation1766_zero, Shared.RelationChunk049.relation1767_zero, Shared.RelationChunk049.relation1768_zero, Shared.RelationChunk049.relation1769_zero, Shared.RelationChunk049.relation1770_zero, Shared.RelationChunk049.relation1771_zero, Shared.RelationChunk049.relation1773_zero, Shared.RelationChunk049.relation1774_zero, Shared.RelationChunk050.relation1775_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14722 128 := by cbv
private def targetRows : List BasisRow := [⟨35, 194, 4, "0,5,64,3"⟩,
  ⟨34, 194, 0, "8,2,64,1,160,1"⟩,
  ⟨34, 194, 1, "8,3,13,1,248,1"⟩,
  ⟨34, 194, 2, "8,4,278,1"⟩,
  ⟨34, 194, 3, "0,5,64,1,299,1"⟩,
  ⟨33, 194, 0, "8,2,624,1"⟩,
  ⟨33, 194, 1, "8,2,13,2,219,1"⟩,
  ⟨33, 194, 2, "8,3,454,1"⟩,
  ⟨32, 194, 0, "8,1,13,3,194,1"⟩,
  ⟨32, 194, 1, "8,2,20,1,292,1"⟩,
  ⟨32, 194, 2, "8,3,455,1"⟩,
  ⟨32, 194, 3, "0,5,64,1,301,1"⟩,
  ⟨31, 194, 0, "13,4,167,1"⟩,
  ⟨31, 194, 1, "8,2,625,1"⟩,
  ⟨31, 194, 2, "8,2,9,1,420,1"⟩,
  ⟨31, 194, 3, "0,6,976,1"⟩,
  ⟨30, 194, 0, "13,4,168,1"⟩,
  ⟨30, 194, 1, "8,1,9,1,13,1,346,1"⟩,
  ⟨30, 194, 2, "8,4,279,1"⟩,
  ⟨29, 194, 1, "9,1,13,2,292,1"⟩,
  ⟨29, 194, 2, "8,4,280,1"⟩,
  ⟨28, 194, 2, "8,3,9,1,261,1"⟩,
  ⟨28, 194, 3, "2,1,1010,1"⟩,
  ⟨27, 194, 0, "138,1,209,1"⟩,
  ⟨27, 194, 1, "17,1,690,1"⟩,
  ⟨27, 194, 3, "8,2,9,1,423,1"⟩,
  ⟨26, 194, 0, "1078,1"⟩,
  ⟨26, 194, 1, "64,1,348,1"⟩,
  ⟨26, 194, 2, "23,1,627,1"⟩,
  ⟨26, 194, 3, "8,1,9,1,13,2,209,1"⟩,
  ⟨25, 194, 1, "1079,1"⟩,
  ⟨25, 194, 2, "64,1,349,1"⟩,
  ⟨25, 194, 3, "9,1,13,2,294,1"⟩,
  ⟨25, 194, 4, "8,1,834,1"⟩,
  ⟨25, 194, 5, "0,2,1049,1"⟩,
  ⟨24, 194, 1, "23,1,628,1"⟩,
  ⟨24, 194, 2, "8,1,79,1,209,1"⟩,
  ⟨24, 194, 3, "0,1,1063,1"⟩,
  ⟨24, 194, 4, "0,2,65,1,324,1"⟩,
  ⟨23, 194, 1, "24,1,628,1"⟩,
  ⟨23, 194, 2, "8,1,80,1,209,1"⟩,
  ⟨23, 194, 3, "0,2,1051,1"⟩,
  ⟨22, 194, 0, "1084,1"⟩,
  ⟨22, 194, 2, "23,1,629,1"⟩,
  ⟨22, 194, 3, "13,1,761,1"⟩,
  ⟨22, 194, 4, "1,1,1051,1"⟩,
  ⟨21, 194, 2, "24,1,629,1"⟩,
  ⟨21, 194, 4, "0,1,1064,1"⟩,
  ⟨21, 194, 5, "0,4,1015,1"⟩,
  ⟨20, 194, 0, "3,1,960,1"⟩,
  ⟨20, 194, 2, "0,1,1066,1"⟩,
  ⟨20, 194, 3, "0,6,59,1,324,1"⟩,
  ⟨19, 194, 0, "8,1,841,1"⟩,
  ⟨19, 194, 1, "0,1,1068,1"⟩,
  ⟨19, 194, 2, "0,1,1067,1"⟩,
  ⟨19, 194, 3, "0,1,2,1,1002,1"⟩,
  ⟨18, 194, 1, "1085,1"⟩,
  ⟨18, 194, 2, "67,1,336,1"⟩,
  ⟨18, 194, 3, "8,1,842,1"⟩,
  ⟨17, 194, 1, "0,1,1069,1"⟩,
  ⟨17, 194, 2, "0,1,67,1,333,1"⟩,
  ⟨16, 194, 1, "8,2,17,1,324,1"⟩,
  ⟨16, 194, 2, "0,1,1071,1"⟩,
  ⟨16, 194, 3, "0,2,1056,1"⟩,
  ⟨16, 194, 4, "0,2,1055,1"⟩,
  ⟨15, 194, 1, "16,1,23,1,324,1"⟩,
  ⟨15, 194, 3, "0,1,1073,1"⟩,
  ⟨15, 194, 4, "0,2,1057,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8740_mem, Shared.BasisChunk008.row8741_mem, Shared.BasisChunk008.row8742_mem, Shared.BasisChunk008.row8743_mem, Shared.BasisChunk008.row8744_mem, Shared.BasisChunk008.row8745_mem, Shared.BasisChunk008.row8746_mem, Shared.BasisChunk008.row8747_mem, Shared.BasisChunk008.row8748_mem, Shared.BasisChunk008.row8749_mem, Shared.BasisChunk008.row8750_mem, Shared.BasisChunk008.row8751_mem, Shared.BasisChunk008.row8752_mem, Shared.BasisChunk008.row8753_mem, Shared.BasisChunk008.row8754_mem, Shared.BasisChunk008.row8755_mem, Shared.BasisChunk008.row8756_mem, Shared.BasisChunk008.row8757_mem, Shared.BasisChunk008.row8758_mem, Shared.BasisChunk008.row8760_mem, Shared.BasisChunk008.row8761_mem, Shared.BasisChunk008.row8764_mem, Shared.BasisChunk008.row8765_mem, Shared.BasisChunk008.row8766_mem, Shared.BasisChunk008.row8767_mem, Shared.BasisChunk008.row8769_mem, Shared.BasisChunk008.row8770_mem, Shared.BasisChunk008.row8771_mem, Shared.BasisChunk008.row8772_mem, Shared.BasisChunk008.row8773_mem, Shared.BasisChunk008.row8775_mem, Shared.BasisChunk008.row8776_mem, Shared.BasisChunk008.row8777_mem, Shared.BasisChunk008.row8778_mem, Shared.BasisChunk008.row8779_mem, Shared.BasisChunk008.row8781_mem, Shared.BasisChunk008.row8782_mem, Shared.BasisChunk008.row8783_mem, Shared.BasisChunk008.row8784_mem, Shared.BasisChunk008.row8786_mem, Shared.BasisChunk008.row8787_mem, Shared.BasisChunk008.row8788_mem, Shared.BasisChunk008.row8789_mem, Shared.BasisChunk008.row8791_mem, Shared.BasisChunk008.row8792_mem, Shared.BasisChunk008.row8793_mem, Shared.BasisChunk008.row8797_mem, Shared.BasisChunk008.row8799_mem, Shared.BasisChunk008.row8800_mem, Shared.BasisChunk008.row8801_mem, Shared.BasisChunk008.row8803_mem, Shared.BasisChunk008.row8804_mem, Shared.BasisChunk008.row8805_mem, Shared.BasisChunk008.row8806_mem, Shared.BasisChunk008.row8807_mem, Shared.BasisChunk008.row8808_mem, Shared.BasisChunk008.row8810_mem, Shared.BasisChunk008.row8811_mem, Shared.BasisChunk008.row8812_mem, Shared.BasisChunk008.row8814_mem, Shared.BasisChunk008.row8815_mem, Shared.BasisChunk008.row8817_mem, Shared.BasisChunk008.row8818_mem, Shared.BasisChunk008.row8819_mem, Shared.BasisChunk008.row8820_mem, Shared.BasisChunk008.row8822_mem, Shared.BasisChunk008.row8824_mem, Shared.BasisChunk008.row8825_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard115
