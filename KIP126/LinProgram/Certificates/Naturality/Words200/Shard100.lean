import KIP126.LinProgram.Generated.Naturality.Words200.Shard100
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk037
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk038
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk039
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard100
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard100
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
  exact ⟨Shared.RelationChunk000.relation7_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation23_zero, Shared.RelationChunk000.relation32_zero, Shared.RelationChunk000.relation33_zero, Shared.RelationChunk000.relation59_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation66_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk003.relation259_zero, Shared.RelationChunk005.relation336_zero, Shared.RelationChunk005.relation340_zero, Shared.RelationChunk008.relation446_zero, Shared.RelationChunk008.relation448_zero, Shared.RelationChunk008.relation484_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk010.relation568_zero, Shared.RelationChunk013.relation668_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk014.relation709_zero, Shared.RelationChunk014.relation711_zero, Shared.RelationChunk014.relation712_zero, Shared.RelationChunk014.relation719_zero, Shared.RelationChunk014.relation720_zero, Shared.RelationChunk014.relation721_zero, Shared.RelationChunk015.relation786_zero, Shared.RelationChunk020.relation918_zero, Shared.RelationChunk020.relation920_zero, Shared.RelationChunk023.relation1034_zero, Shared.RelationChunk024.relation1037_zero, Shared.RelationChunk024.relation1038_zero, Shared.RelationChunk024.relation1039_zero, Shared.RelationChunk024.relation1040_zero, Shared.RelationChunk024.relation1041_zero, Shared.RelationChunk024.relation1042_zero, Shared.RelationChunk024.relation1043_zero, Shared.RelationChunk024.relation1044_zero, Shared.RelationChunk024.relation1050_zero, Shared.RelationChunk024.relation1051_zero, Shared.RelationChunk034.relation1399_zero, Shared.RelationChunk037.relation1486_zero, Shared.RelationChunk037.relation1487_zero, Shared.RelationChunk037.relation1488_zero, Shared.RelationChunk038.relation1537_zero, Shared.RelationChunk039.relation1538_zero, Shared.RelationChunk039.relation1539_zero, Shared.RelationChunk039.relation1542_zero, Shared.RelationChunk039.relation1543_zero, Shared.RelationChunk039.relation1544_zero, Shared.RelationChunk039.relation1545_zero, Shared.RelationChunk039.relation1546_zero, Shared.RelationChunk039.relation1547_zero, Shared.RelationChunk039.relation1548_zero, Shared.RelationChunk039.relation1549_zero, Shared.RelationChunk039.relation1553_zero, Shared.RelationChunk039.relation1561_zero, Shared.RelationChunk039.relation1562_zero, Shared.RelationChunk039.relation1563_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12802 128 := by cbv
private def targetRows : List BasisRow := [⟨41, 185, 0, "8,1,724,1"⟩,
  ⟨41, 185, 1, "0,3,896,1"⟩,
  ⟨40, 185, 0, "8,3,343,1"⟩,
  ⟨40, 185, 1, "0,6,64,1,244,1"⟩,
  ⟨39, 185, 0, "8,2,17,1,257,1"⟩,
  ⟨39, 185, 1, "0,6,138,1,149,1"⟩,
  ⟨38, 185, 1, "8,3,344,1"⟩,
  ⟨37, 185, 0, "8,3,345,1"⟩,
  ⟨37, 185, 1, "0,6,64,1,246,1"⟩,
  ⟨37, 185, 2, "0,6,59,1,260,1"⟩,
  ⟨36, 185, 0, "8,5,160,1"⟩,
  ⟨35, 185, 1, "8,4,232,1"⟩,
  ⟨34, 185, 0, "16,1,64,1,149,1"⟩,
  ⟨34, 185, 1, "8,2,16,1,260,1"⟩,
  ⟨34, 185, 2, "8,4,233,1"⟩,
  ⟨33, 185, 0, "16,1,598,1"⟩,
  ⟨33, 185, 1, "8,2,17,1,260,1"⟩,
  ⟨33, 185, 2, "8,3,9,1,219,1"⟩,
  ⟨33, 185, 3, "0,1,149,2"⟩,
  ⟨32, 185, 0, "16,1,17,1,292,1"⟩,
  ⟨32, 185, 1, "8,1,726,1"⟩,
  ⟨32, 185, 2, "8,2,9,1,13,1,194,1"⟩,
  ⟨32, 185, 3, "0,1,927,1"⟩,
  ⟨31, 185, 0, "8,1,42,1,260,1"⟩,
  ⟨31, 185, 1, "8,1,9,1,13,2,167,1"⟩,
  ⟨31, 185, 2, "8,2,549,1"⟩,
  ⟨31, 185, 3, "0,3,64,1,260,1"⟩,
  ⟨30, 185, 0, "9,1,13,2,248,1"⟩,
  ⟨30, 185, 1, "8,3,347,1"⟩,
  ⟨30, 185, 2, "8,3,346,1"⟩,
  ⟨30, 185, 3, "0,1,64,1,274,1"⟩,
  ⟨30, 185, 4, "0,3,897,1"⟩,
  ⟨29, 185, 0, "8,2,550,1"⟩,
  ⟨29, 185, 1, "8,2,13,1,292,1"⟩,
  ⟨29, 185, 2, "0,2,921,1"⟩,
  ⟨29, 185, 3, "0,2,919,1"⟩,
  ⟨28, 185, 1, "8,1,23,1,346,1"⟩,
  ⟨28, 185, 2, "8,3,348,1"⟩,
  ⟨28, 185, 4, "0,3,898,1"⟩,
  ⟨27, 185, 0, "940,1"⟩,
  ⟨27, 185, 1, "13,1,23,1,292,1"⟩,
  ⟨27, 185, 2, "8,3,350,1"⟩,
  ⟨26, 185, 0, "8,3,13,1,209,1"⟩,
  ⟨25, 185, 0, "8,2,13,1,294,1"⟩,
  ⟨25, 185, 1, "0,1,3,1,832,1"⟩,
  ⟨24, 185, 0, "64,1,279,1"⟩,
  ⟨24, 185, 2, "8,1,13,2,261,1"⟩,
  ⟨24, 185, 3, "0,1,929,1"⟩,
  ⟨23, 185, 1, "64,1,280,1"⟩,
  ⟨23, 185, 2, "13,2,423,1"⟩,
  ⟨23, 185, 3, "0,1,67,1,266,1"⟩,
  ⟨22, 185, 0, "13,2,23,1,181,1"⟩,
  ⟨22, 185, 1, "8,1,729,1"⟩,
  ⟨22, 185, 2, "0,1,930,1"⟩,
  ⟨22, 185, 3, "0,1,67,1,267,1"⟩,
  ⟨21, 185, 0, "942,1"⟩,
  ⟨21, 185, 1, "9,1,692,1"⟩,
  ⟨21, 185, 3, "0,1,68,1,267,1"⟩,
  ⟨21, 185, 4, "0,4,891,1"⟩,
  ⟨20, 185, 0, "944,1"⟩,
  ⟨20, 185, 2, "0,3,908,1"⟩,
  ⟨19, 185, 0, "945,1"⟩,
  ⟨19, 185, 1, "0,1,3,1,838,1"⟩,
  ⟨19, 185, 2, "0,3,50,1,324,1"⟩,
  ⟨18, 185, 0, "946,1"⟩,
  ⟨18, 185, 1, "0,1,932,1"⟩,
  ⟨18, 185, 2, "0,2,3,1,825,1"⟩,
  ⟨17, 185, 0, "947,1"⟩,
  ⟨17, 185, 2, "0,1,3,1,841,1"⟩,
  ⟨16, 185, 0, "948,1"⟩,
  ⟨16, 185, 1, "56,1,324,1"⟩,
  ⟨16, 185, 2, "0,1,3,1,843,1"⟩,
  ⟨15, 185, 0, "1,1,43,1,412,1"⟩,
  ⟨15, 185, 1, "0,1,934,1"⟩,
  ⟨14, 185, 0, "949,1"⟩,
  ⟨14, 185, 1, "3,1,43,1,333,1"⟩,
  ⟨14, 185, 2, "1,1,924,1"⟩,
  ⟨14, 185, 3, "0,1,935,1"⟩,
  ⟨13, 185, 1, "8,2,9,1,324,1"⟩,
  ⟨13, 185, 2, "3,1,861,1"⟩,
  ⟨13, 185, 3, "0,1,937,1"⟩,
  ⟨12, 185, 0, "8,1,29,1,324,1"⟩,
  ⟨12, 185, 1, "2,1,893,1"⟩,
  ⟨12, 185, 2, "0,1,938,1"⟩,
  ⟨11, 185, 0, "9,1,23,1,324,1"⟩,
  ⟨11, 185, 1, "1,1,925,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7623_mem, Shared.BasisChunk007.row7624_mem, Shared.BasisChunk007.row7625_mem, Shared.BasisChunk007.row7626_mem, Shared.BasisChunk007.row7627_mem, Shared.BasisChunk007.row7628_mem, Shared.BasisChunk007.row7630_mem, Shared.BasisChunk007.row7631_mem, Shared.BasisChunk007.row7632_mem, Shared.BasisChunk007.row7633_mem, Shared.BasisChunk007.row7634_mem, Shared.BasisChunk007.row7636_mem, Shared.BasisChunk007.row7637_mem, Shared.BasisChunk007.row7638_mem, Shared.BasisChunk007.row7639_mem, Shared.BasisChunk007.row7640_mem, Shared.BasisChunk007.row7641_mem, Shared.BasisChunk007.row7642_mem, Shared.BasisChunk007.row7643_mem, Shared.BasisChunk007.row7644_mem, Shared.BasisChunk007.row7645_mem, Shared.BasisChunk007.row7646_mem, Shared.BasisChunk007.row7647_mem, Shared.BasisChunk007.row7648_mem, Shared.BasisChunk007.row7649_mem, Shared.BasisChunk007.row7650_mem, Shared.BasisChunk007.row7651_mem, Shared.BasisChunk007.row7652_mem, Shared.BasisChunk007.row7653_mem, Shared.BasisChunk007.row7654_mem, Shared.BasisChunk007.row7655_mem, Shared.BasisChunk007.row7656_mem, Shared.BasisChunk007.row7657_mem, Shared.BasisChunk007.row7658_mem, Shared.BasisChunk007.row7659_mem, Shared.BasisChunk007.row7660_mem, Shared.BasisChunk007.row7662_mem, Shared.BasisChunk007.row7663_mem, Shared.BasisChunk007.row7665_mem, Shared.BasisChunk007.row7666_mem, Shared.BasisChunk007.row7667_mem, Shared.BasisChunk007.row7668_mem, Shared.BasisChunk007.row7669_mem, Shared.BasisChunk007.row7670_mem, Shared.BasisChunk007.row7671_mem, Shared.BasisChunk007.row7672_mem, Shared.BasisChunk007.row7674_mem, Shared.BasisChunk007.row7675_mem, Shared.BasisChunk007.row7677_mem, Shared.BasisChunk007.row7678_mem, Shared.BasisChunk007.row7679_mem, Shared.BasisChunk007.row7680_mem, Shared.BasisChunk007.row7681_mem, Shared.BasisChunk007.row7682_mem, Shared.BasisChunk007.row7683_mem, Shared.BasisChunk007.row7684_mem, Shared.BasisChunk007.row7685_mem, Shared.BasisChunk007.row7687_mem, Shared.BasisChunk007.row7688_mem, Shared.BasisChunk007.row7689_mem, Shared.BasisChunk007.row7691_mem, Shared.BasisChunk007.row7692_mem, Shared.BasisChunk007.row7693_mem, Shared.BasisChunk007.row7694_mem, Shared.BasisChunk007.row7695_mem, Shared.BasisChunk007.row7696_mem, Shared.BasisChunk007.row7697_mem, Shared.BasisChunk007.row7698_mem, Shared.BasisChunk007.row7700_mem, Shared.BasisChunk007.row7701_mem, Shared.BasisChunk007.row7702_mem, Shared.BasisChunk007.row7703_mem, Shared.BasisChunk007.row7704_mem, Shared.BasisChunk007.row7705_mem, Shared.BasisChunk007.row7706_mem, Shared.BasisChunk007.row7707_mem, Shared.BasisChunk007.row7708_mem, Shared.BasisChunk007.row7709_mem, Shared.BasisChunk007.row7711_mem, Shared.BasisChunk007.row7712_mem, Shared.BasisChunk007.row7713_mem, Shared.BasisChunk007.row7714_mem, Shared.BasisChunk007.row7715_mem, Shared.BasisChunk007.row7716_mem, Shared.BasisChunk007.row7717_mem, Shared.BasisChunk007.row7718_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard100
