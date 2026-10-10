import KIP126.LinProgram.Generated.Naturality.Words200.Shard102
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk038
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk040
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard102
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard102
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation16_zero, Shared.RelationChunk000.relation19_zero, Shared.RelationChunk000.relation67_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation75_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk012.relation623_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk014.relation735_zero, Shared.RelationChunk014.relation737_zero, Shared.RelationChunk022.relation990_zero, Shared.RelationChunk022.relation992_zero, Shared.RelationChunk024.relation1057_zero, Shared.RelationChunk038.relation1534_zero, Shared.RelationChunk040.relation1571_zero, Shared.RelationChunk040.relation1572_zero, Shared.RelationChunk040.relation1573_zero, Shared.RelationChunk040.relation1574_zero, Shared.RelationChunk040.relation1575_zero, Shared.RelationChunk040.relation1576_zero, Shared.RelationChunk040.relation1577_zero, Shared.RelationChunk040.relation1578_zero, Shared.RelationChunk040.relation1579_zero, Shared.RelationChunk040.relation1580_zero, Shared.RelationChunk040.relation1581_zero, Shared.RelationChunk040.relation1583_zero, Shared.RelationChunk040.relation1584_zero, Shared.RelationChunk040.relation1585_zero, Shared.RelationChunk040.relation1586_zero, Shared.RelationChunk040.relation1587_zero, Shared.RelationChunk040.relation1588_zero, Shared.RelationChunk040.relation1589_zero, Shared.RelationChunk040.relation1590_zero, Shared.RelationChunk040.relation1591_zero, Shared.RelationChunk040.relation1592_zero, Shared.RelationChunk040.relation1593_zero, Shared.RelationChunk040.relation1594_zero, Shared.RelationChunk040.relation1595_zero, Shared.RelationChunk040.relation1596_zero, Shared.RelationChunk040.relation1597_zero, Shared.RelationChunk040.relation1598_zero, Shared.RelationChunk040.relation1599_zero, Shared.RelationChunk040.relation1600_zero, Shared.RelationChunk040.relation1601_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13058 128 := by cbv
private def targetRows : List BasisRow := [⟨29, 186, 3, "0,4,898,1"⟩,
  ⟨28, 186, 0, "956,1"⟩,
  ⟨28, 186, 1, "8,3,13,1,212,1"⟩,
  ⟨28, 186, 2, "0,1,940,1"⟩,
  ⟨27, 186, 0, "957,1"⟩,
  ⟨27, 186, 1, "8,2,13,2,188,1"⟩,
  ⟨27, 186, 2, "1,2,898,1"⟩,
  ⟨26, 186, 1, "13,1,23,1,303,1"⟩,
  ⟨26, 186, 2, "8,1,64,1,201,1"⟩,
  ⟨26, 186, 3, "8,1,13,2,267,1"⟩,
  ⟨26, 186, 4, "1,1,5,1,64,1,209,1"⟩,
  ⟨26, 186, 5, "0,2,3,1,832,1"⟩,
  ⟨25, 186, 0, "13,2,23,1,188,1"⟩,
  ⟨25, 186, 1, "9,1,13,1,472,1"⟩,
  ⟨25, 186, 2, "8,1,72,1,188,1"⟩,
  ⟨25, 186, 3, "2,1,899,1"⟩,
  ⟨25, 186, 4, "0,1,9,1,690,1"⟩,
  ⟨25, 186, 5, "0,2,929,1"⟩,
  ⟨24, 186, 0, "13,2,23,1,189,1"⟩,
  ⟨24, 186, 1, "8,1,738,1"⟩,
  ⟨24, 186, 2, "2,1,901,1"⟩,
  ⟨24, 186, 3, "0,1,941,1"⟩,
  ⟨23, 186, 0, "9,1,705,1"⟩,
  ⟨23, 186, 1, "1,1,64,1,275,1"⟩,
  ⟨23, 186, 2, "0,2,930,1"⟩,
  ⟨22, 186, 0, "13,2,23,1,190,1"⟩,
  ⟨22, 186, 2, "0,5,891,1"⟩,
  ⟨21, 186, 0, "9,1,13,1,474,1"⟩,
  ⟨21, 186, 1, "0,1,943,1"⟩,
  ⟨21, 186, 2, "0,4,908,1"⟩,
  ⟨20, 186, 2, "0,4,50,1,324,1"⟩,
  ⟨19, 186, 0, "960,1"⟩,
  ⟨19, 186, 1, "1,2,906,1"⟩,
  ⟨19, 186, 3, "0,3,3,1,825,1"⟩,
  ⟨18, 186, 0, "1,1,932,1"⟩,
  ⟨18, 186, 1, "0,1,55,1,324,1"⟩,
  ⟨17, 186, 0, "0,1,56,1,324,1"⟩,
  ⟨17, 186, 1, "0,2,3,1,843,1"⟩,
  ⟨16, 186, 0, "70,1,275,1"⟩,
  ⟨15, 186, 0, "0,2,935,1"⟩,
  ⟨14, 186, 0, "3,2,769,1"⟩,
  ⟨14, 186, 1, "1,1,935,1"⟩,
  ⟨13, 186, 0, "7,1,769,1"⟩,
  ⟨13, 186, 1, "2,1,912,1"⟩,
  ⟨13, 186, 2, "0,2,938,1"⟩,
  ⟨12, 186, 0, "76,1,264,1"⟩,
  ⟨12, 186, 2, "2,1,43,1,396,1"⟩,
  ⟨11, 186, 1, "2,1,43,1,398,1"⟩,
  ⟨11, 186, 2, "1,1,3,1,847,1"⟩,
  ⟨10, 186, 0, "2,1,43,1,400,1"⟩,
  ⟨10, 186, 1, "0,1,13,1,660,1"⟩,
  ⟨9, 186, 0, "3,1,18,1,525,1"⟩,
  ⟨9, 186, 1, "0,1,2,1,894,1"⟩,
  ⟨8, 186, 0, "2,1,913,1"⟩,
  ⟨8, 186, 1, "0,2,3,1,43,1,324,1"⟩,
  ⟨7, 186, 0, "2,1,914,1"⟩,
  ⟨7, 186, 1, "1,1,3,1,43,1,324,1"⟩,
  ⟨6, 186, 0, "2,1,11,1,18,1,324,1"⟩,
  ⟨187, 187, 0, "0,187"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7804_mem, Shared.BasisChunk007.row7805_mem, Shared.BasisChunk007.row7806_mem, Shared.BasisChunk007.row7807_mem, Shared.BasisChunk007.row7808_mem, Shared.BasisChunk007.row7809_mem, Shared.BasisChunk007.row7810_mem, Shared.BasisChunk007.row7812_mem, Shared.BasisChunk007.row7813_mem, Shared.BasisChunk007.row7814_mem, Shared.BasisChunk007.row7815_mem, Shared.BasisChunk007.row7816_mem, Shared.BasisChunk007.row7817_mem, Shared.BasisChunk007.row7818_mem, Shared.BasisChunk007.row7819_mem, Shared.BasisChunk007.row7820_mem, Shared.BasisChunk007.row7821_mem, Shared.BasisChunk007.row7822_mem, Shared.BasisChunk007.row7823_mem, Shared.BasisChunk007.row7824_mem, Shared.BasisChunk007.row7825_mem, Shared.BasisChunk007.row7826_mem, Shared.BasisChunk007.row7827_mem, Shared.BasisChunk007.row7828_mem, Shared.BasisChunk007.row7829_mem, Shared.BasisChunk007.row7830_mem, Shared.BasisChunk007.row7832_mem, Shared.BasisChunk007.row7833_mem, Shared.BasisChunk007.row7834_mem, Shared.BasisChunk007.row7835_mem, Shared.BasisChunk007.row7838_mem, Shared.BasisChunk007.row7839_mem, Shared.BasisChunk007.row7840_mem, Shared.BasisChunk007.row7842_mem, Shared.BasisChunk007.row7843_mem, Shared.BasisChunk007.row7844_mem, Shared.BasisChunk007.row7845_mem, Shared.BasisChunk007.row7846_mem, Shared.BasisChunk007.row7847_mem, Shared.BasisChunk007.row7848_mem, Shared.BasisChunk007.row7849_mem, Shared.BasisChunk007.row7850_mem, Shared.BasisChunk007.row7851_mem, Shared.BasisChunk007.row7852_mem, Shared.BasisChunk007.row7853_mem, Shared.BasisChunk007.row7854_mem, Shared.BasisChunk007.row7856_mem, Shared.BasisChunk007.row7859_mem, Shared.BasisChunk007.row7860_mem, Shared.BasisChunk007.row7861_mem, Shared.BasisChunk007.row7862_mem, Shared.BasisChunk007.row7863_mem, Shared.BasisChunk007.row7864_mem, Shared.BasisChunk007.row7865_mem, Shared.BasisChunk007.row7866_mem, Shared.BasisChunk007.row7867_mem, Shared.BasisChunk007.row7868_mem, Shared.BasisChunk007.row7869_mem, Shared.BasisChunk007.row7870_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard102
