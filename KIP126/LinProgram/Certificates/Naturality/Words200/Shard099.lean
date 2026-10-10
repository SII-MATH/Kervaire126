import KIP126.LinProgram.Generated.Naturality.Words200.Shard099
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk036
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk038
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk039
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk040
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard099
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard099
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
  exact ⟨Shared.RelationChunk000.relation26_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk004.relation304_zero, Shared.RelationChunk013.relation699_zero, Shared.RelationChunk013.relation700_zero, Shared.RelationChunk023.relation1029_zero, Shared.RelationChunk036.relation1459_zero, Shared.RelationChunk038.relation1523_zero, Shared.RelationChunk038.relation1524_zero, Shared.RelationChunk038.relation1525_zero, Shared.RelationChunk038.relation1526_zero, Shared.RelationChunk038.relation1527_zero, Shared.RelationChunk038.relation1528_zero, Shared.RelationChunk038.relation1529_zero, Shared.RelationChunk038.relation1530_zero, Shared.RelationChunk038.relation1531_zero, Shared.RelationChunk038.relation1532_zero, Shared.RelationChunk038.relation1533_zero, Shared.RelationChunk038.relation1535_zero, Shared.RelationChunk038.relation1536_zero, Shared.RelationChunk039.relation1564_zero, Shared.RelationChunk039.relation1565_zero, Shared.RelationChunk039.relation1566_zero, Shared.RelationChunk040.relation1567_zero, Shared.RelationChunk040.relation1568_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12674 128 := by cbv
private def targetRows : List BasisRow := [⟨28, 184, 0, "13,1,642,1"⟩,
  ⟨28, 184, 1, "0,1,921,1"⟩,
  ⟨28, 184, 2, "0,1,919,1"⟩,
  ⟨27, 184, 0, "23,1,537,1"⟩,
  ⟨27, 184, 1, "13,5,67,1"⟩,
  ⟨27, 184, 2, "0,2,898,1"⟩,
  ⟨26, 184, 0, "9,1,13,4,75,1"⟩,
  ⟨26, 184, 1, "8,1,69,1,185,1"⟩,
  ⟨26, 184, 3, "0,2,8,1,690,1"⟩,
  ⟨25, 184, 2, "0,2,903,1"⟩,
  ⟨25, 184, 3, "0,2,901,1"⟩,
  ⟨24, 184, 1, "0,1,922,1"⟩,
  ⟨24, 184, 2, "0,1,2,1,876,1"⟩,
  ⟨23, 184, 0, "929,1"⟩,
  ⟨23, 184, 1, "1,1,13,1,628,1"⟩,
  ⟨22, 184, 0, "67,1,266,1"⟩,
  ⟨22, 184, 2, "1,1,8,1,692,1"⟩,
  ⟨21, 184, 1, "67,1,267,1"⟩,
  ⟨21, 184, 2, "13,2,417,1"⟩,
  ⟨20, 184, 0, "68,1,267,1"⟩,
  ⟨20, 184, 1, "9,1,677,1"⟩,
  ⟨20, 184, 2, "0,3,891,1"⟩,
  ⟨19, 184, 1, "0,2,908,1"⟩,
  ⟨19, 184, 2, "0,2,49,1,324,1"⟩,
  ⟨18, 184, 0, "9,1,13,1,450,1"⟩,
  ⟨18, 184, 1, "3,1,838,1"⟩,
  ⟨18, 184, 4, "0,2,50,1,324,1"⟩,
  ⟨17, 184, 1, "1,1,909,1"⟩,
  ⟨17, 184, 2, "0,1,3,1,825,1"⟩,
  ⟨16, 184, 1, "0,1,3,2,730,1"⟩,
  ⟨16, 184, 2, "0,2,911,1"⟩,
  ⟨15, 184, 0, "933,1"⟩,
  ⟨15, 184, 1, "3,1,843,1"⟩,
  ⟨15, 184, 2, "3,1,842,1"⟩,
  ⟨15, 184, 3, "0,2,8,3,324,1"⟩,
  ⟨15, 184, 4, "0,2,3,1,817,1"⟩,
  ⟨14, 184, 0, "934,1"⟩,
  ⟨14, 184, 1, "0,2,8,1,22,1,324,1"⟩,
  ⟨14, 184, 2, "0,3,893,1"⟩,
  ⟨13, 184, 0, "936,1"⟩,
  ⟨12, 184, 0, "937,1"⟩,
  ⟨12, 184, 1, "1,1,18,1,563,1"⟩,
  ⟨11, 184, 1, "7,1,746,1"⟩,
  ⟨10, 184, 1, "0,3,894,1"⟩,
  ⟨9, 184, 0, "0,1,53,1,324,1"⟩,
  ⟨7, 184, 0, "54,1,324,1"⟩,
  ⟨6, 184, 1, "2,2,849,1"⟩,
  ⟨5, 184, 0, "2,2,850,1"⟩,
  ⟨185, 185, 0, "0,185"⟩,
  ⟨62, 185, 0, "0,1,926,1"⟩,
  ⟨59, 185, 0, "0,5,17,1,554,1"⟩,
  ⟨58, 185, 0, "0,2,8,1,700,1"⟩,
  ⟨58, 185, 1, "0,57,324,1"⟩,
  ⟨57, 185, 0, "0,2,8,1,701,1"⟩,
  ⟨52, 185, 0, "0,2,916,1"⟩,
  ⟨51, 185, 1, "0,2,917,1"⟩,
  ⟨48, 185, 0, "0,2,8,1,16,1,402,1"⟩,
  ⟨47, 185, 0, "0,2,8,1,16,1,403,1"⟩,
  ⟨44, 185, 2, "0,11,807,1"⟩,
  ⟨43, 185, 0, "17,1,595,1"⟩,
  ⟨43, 185, 1, "0,12,795,1"⟩,
  ⟨42, 185, 0, "8,1,723,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7543_mem, Shared.BasisChunk007.row7544_mem, Shared.BasisChunk007.row7545_mem, Shared.BasisChunk007.row7546_mem, Shared.BasisChunk007.row7547_mem, Shared.BasisChunk007.row7548_mem, Shared.BasisChunk007.row7549_mem, Shared.BasisChunk007.row7550_mem, Shared.BasisChunk007.row7552_mem, Shared.BasisChunk007.row7555_mem, Shared.BasisChunk007.row7556_mem, Shared.BasisChunk007.row7558_mem, Shared.BasisChunk007.row7559_mem, Shared.BasisChunk007.row7560_mem, Shared.BasisChunk007.row7561_mem, Shared.BasisChunk007.row7562_mem, Shared.BasisChunk007.row7564_mem, Shared.BasisChunk007.row7566_mem, Shared.BasisChunk007.row7567_mem, Shared.BasisChunk007.row7568_mem, Shared.BasisChunk007.row7569_mem, Shared.BasisChunk007.row7570_mem, Shared.BasisChunk007.row7572_mem, Shared.BasisChunk007.row7573_mem, Shared.BasisChunk007.row7574_mem, Shared.BasisChunk007.row7575_mem, Shared.BasisChunk007.row7578_mem, Shared.BasisChunk007.row7580_mem, Shared.BasisChunk007.row7581_mem, Shared.BasisChunk007.row7583_mem, Shared.BasisChunk007.row7584_mem, Shared.BasisChunk007.row7585_mem, Shared.BasisChunk007.row7586_mem, Shared.BasisChunk007.row7587_mem, Shared.BasisChunk007.row7588_mem, Shared.BasisChunk007.row7589_mem, Shared.BasisChunk007.row7590_mem, Shared.BasisChunk007.row7591_mem, Shared.BasisChunk007.row7592_mem, Shared.BasisChunk007.row7593_mem, Shared.BasisChunk007.row7595_mem, Shared.BasisChunk007.row7596_mem, Shared.BasisChunk007.row7598_mem, Shared.BasisChunk007.row7600_mem, Shared.BasisChunk007.row7601_mem, Shared.BasisChunk007.row7602_mem, Shared.BasisChunk007.row7604_mem, Shared.BasisChunk007.row7605_mem, Shared.BasisChunk007.row7606_mem, Shared.BasisChunk007.row7607_mem, Shared.BasisChunk007.row7608_mem, Shared.BasisChunk007.row7609_mem, Shared.BasisChunk007.row7610_mem, Shared.BasisChunk007.row7611_mem, Shared.BasisChunk007.row7612_mem, Shared.BasisChunk007.row7614_mem, Shared.BasisChunk007.row7615_mem, Shared.BasisChunk007.row7616_mem, Shared.BasisChunk007.row7619_mem, Shared.BasisChunk007.row7620_mem, Shared.BasisChunk007.row7621_mem, Shared.BasisChunk007.row7622_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard099
