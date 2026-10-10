import KIP126.LinProgram.Generated.Naturality.Words200.Shard090
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard090
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard090
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation17_zero, Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation52_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation104_zero, Shared.RelationChunk000.relation114_zero, Shared.RelationChunk002.relation211_zero, Shared.RelationChunk003.relation271_zero, Shared.RelationChunk004.relation316_zero, Shared.RelationChunk008.relation472_zero, Shared.RelationChunk010.relation550_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk011.relation604_zero, Shared.RelationChunk011.relation605_zero, Shared.RelationChunk011.relation608_zero, Shared.RelationChunk011.relation609_zero, Shared.RelationChunk011.relation610_zero, Shared.RelationChunk011.relation612_zero, Shared.RelationChunk011.relation613_zero, Shared.RelationChunk011.relation614_zero, Shared.RelationChunk011.relation615_zero, Shared.RelationChunk011.relation616_zero, Shared.RelationChunk011.relation617_zero, Shared.RelationChunk016.relation811_zero, Shared.RelationChunk017.relation812_zero, Shared.RelationChunk020.relation917_zero, Shared.RelationChunk020.relation918_zero, Shared.RelationChunk020.relation920_zero, Shared.RelationChunk020.relation921_zero, Shared.RelationChunk020.relation922_zero, Shared.RelationChunk020.relation923_zero, Shared.RelationChunk020.relation924_zero, Shared.RelationChunk020.relation925_zero, Shared.RelationChunk020.relation926_zero, Shared.RelationChunk020.relation927_zero, Shared.RelationChunk020.relation928_zero, Shared.RelationChunk020.relation929_zero, Shared.RelationChunk020.relation932_zero, Shared.RelationChunk020.relation933_zero, Shared.RelationChunk020.relation934_zero, Shared.RelationChunk020.relation935_zero, Shared.RelationChunk032.relation1341_zero, Shared.RelationChunk032.relation1351_zero, Shared.RelationChunk032.relation1353_zero, Shared.RelationChunk032.relation1354_zero, Shared.RelationChunk032.relation1355_zero, Shared.RelationChunk032.relation1356_zero, Shared.RelationChunk032.relation1357_zero, Shared.RelationChunk032.relation1358_zero, Shared.RelationChunk034.relation1385_zero, Shared.RelationChunk034.relation1387_zero, Shared.RelationChunk034.relation1388_zero, Shared.RelationChunk034.relation1389_zero, Shared.RelationChunk034.relation1390_zero, Shared.RelationChunk034.relation1391_zero, Shared.RelationChunk034.relation1392_zero, Shared.RelationChunk034.relation1393_zero, Shared.RelationChunk034.relation1394_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11522 128 := by cbv
private def targetRows : List BasisRow := [⟨10, 178, 0, "18,1,523,1"⟩,
  ⟨10, 178, 1, "3,1,774,1"⟩,
  ⟨10, 178, 2, "1,1,847,1"⟩,
  ⟨10, 178, 3, "0,2,848,1"⟩,
  ⟨9, 178, 0, "18,1,524,1"⟩,
  ⟨9, 178, 2, "3,1,776,1"⟩,
  ⟨9, 178, 3, "0,2,6,1,18,1,324,1"⟩,
  ⟨8, 178, 0, "18,1,525,1"⟩,
  ⟨8, 178, 1, "0,2,18,1,506,1"⟩,
  ⟨7, 178, 1, "0,2,43,1,324,1"⟩,
  ⟨7, 178, 2, "0,2,3,1,751,1"⟩,
  ⟨6, 178, 1, "1,1,43,1,324,1"⟩,
  ⟨6, 178, 2, "0,2,849,1"⟩,
  ⟨5, 178, 1, "0,2,850,1"⟩,
  ⟨179, 179, 0, "0,179"⟩,
  ⟨60, 179, 0, "0,5,804,1"⟩,
  ⟨58, 179, 0, "0,2,851,1"⟩,
  ⟨57, 179, 0, "0,2,852,1"⟩,
  ⟨53, 179, 0, "0,15,686,1"⟩,
  ⟨52, 179, 0, "0,51,324,1"⟩,
  ⟨48, 179, 0, "0,2,8,1,635,1"⟩,
  ⟨47, 179, 0, "0,2,8,1,636,1"⟩,
  ⟨43, 179, 0, "0,2,8,2,16,1,225,1"⟩,
  ⟨41, 179, 0, "873,1"⟩,
  ⟨41, 179, 1, "0,5,64,1,224,1"⟩,
  ⟨40, 179, 0, "8,2,488,1"⟩,
  ⟨40, 179, 1, "0,5,64,1,225,1"⟩,
  ⟨39, 179, 0, "8,1,17,1,343,1"⟩,
  ⟨38, 179, 0, "8,2,489,1"⟩,
  ⟨38, 179, 1, "0,5,809,1"⟩,
  ⟨38, 179, 2, "0,5,807,1"⟩,
  ⟨37, 179, 0, "8,2,490,1"⟩,
  ⟨37, 179, 1, "0,2,64,1,238,1"⟩,
  ⟨37, 179, 2, "0,6,795,1"⟩,
  ⟨36, 179, 0, "8,4,206,1"⟩,
  ⟨35, 179, 0, "8,3,17,1,160,1"⟩,
  ⟨34, 179, 2, "8,4,207,1"⟩,
  ⟨33, 179, 0, "138,1,149,1"⟩,
  ⟨33, 179, 1, "16,1,17,1,260,1"⟩,
  ⟨33, 179, 2, "8,4,208,1"⟩,
  ⟨32, 179, 0, "64,1,245,1"⟩,
  ⟨32, 179, 1, "17,2,260,1"⟩,
  ⟨32, 179, 2, "8,3,9,1,194,1"⟩,
  ⟨31, 179, 0, "64,1,246,1"⟩,
  ⟨31, 179, 1, "60,1,260,1"⟩,
  ⟨31, 179, 2, "59,1,260,1"⟩,
  ⟨31, 179, 3, "8,1,653,1"⟩,
  ⟨31, 179, 4, "8,2,9,1,13,1,167,1"⟩,
  ⟨30, 179, 0, "8,1,16,1,347,1"⟩,
  ⟨30, 179, 1, "8,1,9,1,13,1,248,1"⟩,
  ⟨30, 179, 2, "8,3,291,1"⟩,
  ⟨30, 179, 3, "0,1,862,1"⟩,
  ⟨29, 179, 0, "9,1,13,2,219,1"⟩,
  ⟨29, 179, 1, "8,1,17,1,347,1"⟩,
  ⟨29, 179, 2, "8,3,292,1"⟩,
  ⟨28, 179, 0, "8,1,22,1,292,1"⟩,
  ⟨28, 179, 1, "8,2,492,1"⟩,
  ⟨27, 179, 0, "8,1,23,1,292,1"⟩,
  ⟨27, 179, 1, "8,3,293,1"⟩,
  ⟨27, 179, 3, "0,2,853,1"⟩,
  ⟨26, 179, 0, "13,2,346,1"⟩,
  ⟨26, 179, 1, "8,4,209,1"⟩,
  ⟨26, 179, 2, "0,2,855,1"⟩,
  ⟨25, 179, 0, "8,3,294,1"⟩,
  ⟨24, 179, 1, "8,2,13,1,261,1"⟩,
  ⟨23, 179, 1, "874,1"⟩,
  ⟨23, 179, 2, "8,1,13,1,423,1"⟩,
  ⟨22, 179, 0, "876,1"⟩,
  ⟨22, 179, 1, "64,1,250,1"⟩,
  ⟨22, 179, 2, "13,3,209,1"⟩,
  ⟨22, 179, 3, "0,2,8,1,17,1,333,1"⟩,
  ⟨22, 179, 4, "0,3,64,1,235,1"⟩,
  ⟨22, 179, 5, "0,11,743,1"⟩,
  ⟨21, 179, 0, "878,1"⟩,
  ⟨21, 179, 2, "13,2,67,1,75,1"⟩,
  ⟨21, 179, 4, "0,3,837,1"⟩,
  ⟨21, 179, 5, "0,3,836,1"⟩,
  ⟨20, 179, 1, "2,1,822,1"⟩,
  ⟨20, 179, 3, "0,3,838,1"⟩,
  ⟨19, 179, 1, "0,1,865,1"⟩,
  ⟨19, 179, 2, "0,4,825,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6869_mem, Shared.BasisChunk006.row6870_mem, Shared.BasisChunk006.row6871_mem, Shared.BasisChunk006.row6872_mem, Shared.BasisChunk006.row6873_mem, Shared.BasisChunk006.row6875_mem, Shared.BasisChunk006.row6876_mem, Shared.BasisChunk006.row6877_mem, Shared.BasisChunk006.row6878_mem, Shared.BasisChunk006.row6880_mem, Shared.BasisChunk006.row6881_mem, Shared.BasisChunk006.row6883_mem, Shared.BasisChunk006.row6884_mem, Shared.BasisChunk006.row6886_mem, Shared.BasisChunk006.row6888_mem, Shared.BasisChunk006.row6889_mem, Shared.BasisChunk006.row6891_mem, Shared.BasisChunk006.row6892_mem, Shared.BasisChunk006.row6893_mem, Shared.BasisChunk006.row6894_mem, Shared.BasisChunk006.row6895_mem, Shared.BasisChunk006.row6896_mem, Shared.BasisChunk006.row6898_mem, Shared.BasisChunk006.row6900_mem, Shared.BasisChunk006.row6901_mem, Shared.BasisChunk006.row6902_mem, Shared.BasisChunk006.row6903_mem, Shared.BasisChunk006.row6904_mem, Shared.BasisChunk006.row6905_mem, Shared.BasisChunk006.row6906_mem, Shared.BasisChunk006.row6907_mem, Shared.BasisChunk006.row6908_mem, Shared.BasisChunk006.row6909_mem, Shared.BasisChunk006.row6910_mem, Shared.BasisChunk006.row6911_mem, Shared.BasisChunk006.row6912_mem, Shared.BasisChunk006.row6915_mem, Shared.BasisChunk006.row6916_mem, Shared.BasisChunk006.row6917_mem, Shared.BasisChunk006.row6918_mem, Shared.BasisChunk006.row6919_mem, Shared.BasisChunk006.row6920_mem, Shared.BasisChunk006.row6921_mem, Shared.BasisChunk006.row6922_mem, Shared.BasisChunk006.row6923_mem, Shared.BasisChunk006.row6924_mem, Shared.BasisChunk006.row6925_mem, Shared.BasisChunk006.row6926_mem, Shared.BasisChunk006.row6927_mem, Shared.BasisChunk006.row6928_mem, Shared.BasisChunk006.row6929_mem, Shared.BasisChunk006.row6930_mem, Shared.BasisChunk006.row6931_mem, Shared.BasisChunk006.row6932_mem, Shared.BasisChunk006.row6933_mem, Shared.BasisChunk006.row6934_mem, Shared.BasisChunk006.row6935_mem, Shared.BasisChunk006.row6936_mem, Shared.BasisChunk006.row6937_mem, Shared.BasisChunk006.row6939_mem, Shared.BasisChunk006.row6940_mem, Shared.BasisChunk006.row6941_mem, Shared.BasisChunk006.row6942_mem, Shared.BasisChunk006.row6943_mem, Shared.BasisChunk006.row6945_mem, Shared.BasisChunk006.row6948_mem, Shared.BasisChunk006.row6949_mem, Shared.BasisChunk006.row6950_mem, Shared.BasisChunk006.row6951_mem, Shared.BasisChunk006.row6952_mem, Shared.BasisChunk006.row6953_mem, Shared.BasisChunk006.row6954_mem, Shared.BasisChunk006.row6955_mem, Shared.BasisChunk006.row6956_mem, Shared.BasisChunk006.row6958_mem, Shared.BasisChunk006.row6960_mem, Shared.BasisChunk006.row6961_mem, Shared.BasisChunk006.row6963_mem, Shared.BasisChunk006.row6965_mem, Shared.BasisChunk006.row6967_mem, Shared.BasisChunk006.row6968_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard090
