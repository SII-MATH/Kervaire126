import KIP126.LinProgram.Generated.Naturality.Words200.Shard123
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk051
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk053
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk054
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk055
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk009

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard123
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard123
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationsFirst.relation1_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation39_zero, Shared.RelationChunk000.relation40_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation89_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk001.relation143_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation207_zero, Shared.RelationChunk001.relation208_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation228_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk007.relation411_zero, Shared.RelationChunk007.relation412_zero, Shared.RelationChunk007.relation422_zero, Shared.RelationChunk009.relation486_zero, Shared.RelationChunk009.relation489_zero, Shared.RelationChunk009.relation492_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk012.relation623_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk012.relation625_zero, Shared.RelationChunk012.relation626_zero, Shared.RelationChunk014.relation736_zero, Shared.RelationChunk017.relation834_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk017.relation845_zero, Shared.RelationChunk020.relation941_zero, Shared.RelationChunk021.relation945_zero, Shared.RelationChunk021.relation946_zero, Shared.RelationChunk021.relation947_zero, Shared.RelationChunk031.relation1321_zero, Shared.RelationChunk032.relation1329_zero, Shared.RelationChunk034.relation1386_zero, Shared.RelationChunk034.relation1420_zero, Shared.RelationChunk034.relation1430_zero, Shared.RelationChunk051.relation1800_zero, Shared.RelationChunk051.relation1801_zero, Shared.RelationChunk051.relation1819_zero, Shared.RelationChunk053.relation1842_zero, Shared.RelationChunk053.relation1843_zero, Shared.RelationChunk053.relation1844_zero, Shared.RelationChunk053.relation1845_zero, Shared.RelationChunk053.relation1846_zero, Shared.RelationChunk053.relation1847_zero, Shared.RelationChunk053.relation1848_zero, Shared.RelationChunk053.relation1851_zero, Shared.RelationChunk053.relation1852_zero, Shared.RelationChunk053.relation1853_zero, Shared.RelationChunk053.relation1854_zero, Shared.RelationChunk053.relation1855_zero, Shared.RelationChunk053.relation1856_zero, Shared.RelationChunk054.relation1903_zero, Shared.RelationChunk054.relation1904_zero, Shared.RelationChunk054.relation1905_zero, Shared.RelationChunk054.relation1906_zero, Shared.RelationChunk054.relation1907_zero, Shared.RelationChunk054.relation1908_zero, Shared.RelationChunk054.relation1909_zero, Shared.RelationChunk054.relation1910_zero, Shared.RelationChunk054.relation1911_zero, Shared.RelationChunk055.relation1912_zero, Shared.RelationChunk055.relation1913_zero, Shared.RelationChunk055.relation1914_zero, Shared.RelationChunk055.relation1915_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15746 128 := by cbv
private def targetRows : List BasisRow := [⟨34, 198, 0, "8,1,13,6,23,1"⟩,
  ⟨34, 198, 1, "8,3,499,1"⟩,
  ⟨34, 198, 2, "8,3,9,1,13,2,101,1"⟩,
  ⟨33, 198, 0, "13,6,51,1"⟩,
  ⟨33, 198, 1, "8,2,13,1,435,1"⟩,
  ⟨33, 198, 2, "8,2,9,1,13,3,80,1"⟩,
  ⟨33, 198, 3, "0,1,64,1,380,1"⟩,
  ⟨32, 198, 1, "13,6,52,1"⟩,
  ⟨32, 198, 2, "8,1,9,1,13,2,23,1,101,1"⟩,
  ⟨32, 198, 3, "8,5,212,1"⟩,
  ⟨32, 198, 4, "0,1,113,1,260,1"⟩,
  ⟨32, 198, 5, "0,4,64,1,347,1"⟩,
  ⟨31, 198, 0, "1145,1"⟩,
  ⟨31, 198, 1, "9,1,13,3,23,1,80,1"⟩,
  ⟨31, 198, 2, "8,4,13,1,188,1"⟩,
  ⟨31, 198, 3, "0,2,1103,1"⟩,
  ⟨31, 198, 4, "0,4,138,1,209,1"⟩,
  ⟨30, 198, 0, "8,1,64,1,254,1"⟩,
  ⟨30, 198, 1, "8,3,13,1,267,1"⟩,
  ⟨30, 198, 3, "0,4,23,1,627,1"⟩,
  ⟨29, 198, 0, "8,1,64,1,255,1"⟩,
  ⟨29, 198, 1, "8,2,13,1,23,1,188,1"⟩,
  ⟨29, 198, 2, "0,1,8,2,655,1"⟩,
  ⟨29, 198, 3, "0,4,1079,1"⟩,
  ⟨29, 198, 4, "0,4,64,1,349,1"⟩,
  ⟨28, 198, 0, "13,3,303,1"⟩,
  ⟨28, 198, 1, "8,1,13,3,212,1"⟩,
  ⟨28, 198, 2, "8,2,667,1"⟩,
  ⟨28, 198, 3, "0,1,8,1,874,1"⟩,
  ⟨28, 198, 4, "0,4,1081,1"⟩,
  ⟨28, 198, 5, "0,5,1063,1"⟩,
  ⟨27, 198, 0, "13,4,188,1"⟩,
  ⟨27, 198, 1, "9,1,13,2,328,1"⟩,
  ⟨27, 198, 2, "8,2,668,1"⟩,
  ⟨27, 198, 3, "0,1,23,1,655,1"⟩,
  ⟨27, 198, 4, "0,2,3,1,978,1"⟩,
  ⟨27, 198, 5, "0,6,1051,1"⟩,
  ⟨26, 198, 0, "13,4,189,1"⟩,
  ⟨26, 198, 1, "8,1,9,1,640,1"⟩,
  ⟨26, 198, 2, "0,1,1122,1"⟩,
  ⟨26, 198, 3, "0,4,1084,1"⟩,
  ⟨25, 198, 0, "9,1,80,1,212,1"⟩,
  ⟨25, 198, 1, "0,2,1105,1"⟩,
  ⟨25, 198, 2, "0,2,67,1,359,1"⟩,
  ⟨24, 198, 0, "13,4,190,1"⟩,
  ⟨24, 198, 2, "0,2,68,1,359,1"⟩,
  ⟨24, 198, 3, "0,10,59,1,324,1"⟩,
  ⟨23, 198, 1, "9,1,13,2,331,1"⟩,
  ⟨23, 198, 2, "2,1,1083,1"⟩,
  ⟨22, 198, 0, "1147,1"⟩,
  ⟨22, 198, 1, "0,1,77,1,324,1"⟩,
  ⟨22, 198, 2, "0,2,1108,1"⟩,
  ⟨21, 198, 0, "1149,1"⟩,
  ⟨21, 198, 1, "1148,1"⟩,
  ⟨21, 198, 2, "1,1,1107,1"⟩,
  ⟨21, 198, 3, "0,1,78,1,324,1"⟩,
  ⟨20, 198, 0, "1151,1"⟩,
  ⟨20, 198, 2, "3,1,1011,1"⟩,
  ⟨20, 198, 3, "1,2,1086,1"⟩,
  ⟨18, 198, 2, "3,1,1016,1"⟩,
  ⟨18, 198, 3, "3,1,1015,1"⟩,
  ⟨18, 198, 4, "0,7,64,1,324,1"⟩,
  ⟨17, 198, 1, "3,1,1017,1"⟩,
  ⟨17, 198, 2, "1,1,1112,1"⟩,
  ⟨17, 198, 3, "1,2,1088,1"⟩,
  ⟨17, 198, 4, "0,1,1129,1"⟩,
  ⟨17, 198, 5, "0,6,66,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk009.row9349_mem, Shared.BasisChunk009.row9350_mem, Shared.BasisChunk009.row9351_mem, Shared.BasisChunk009.row9353_mem, Shared.BasisChunk009.row9354_mem, Shared.BasisChunk009.row9355_mem, Shared.BasisChunk009.row9356_mem, Shared.BasisChunk009.row9358_mem, Shared.BasisChunk009.row9359_mem, Shared.BasisChunk009.row9360_mem, Shared.BasisChunk009.row9361_mem, Shared.BasisChunk009.row9362_mem, Shared.BasisChunk009.row9363_mem, Shared.BasisChunk009.row9364_mem, Shared.BasisChunk009.row9365_mem, Shared.BasisChunk009.row9366_mem, Shared.BasisChunk009.row9367_mem, Shared.BasisChunk009.row9368_mem, Shared.BasisChunk009.row9369_mem, Shared.BasisChunk009.row9371_mem, Shared.BasisChunk009.row9372_mem, Shared.BasisChunk009.row9373_mem, Shared.BasisChunk009.row9374_mem, Shared.BasisChunk009.row9375_mem, Shared.BasisChunk009.row9376_mem, Shared.BasisChunk009.row9377_mem, Shared.BasisChunk009.row9378_mem, Shared.BasisChunk009.row9379_mem, Shared.BasisChunk009.row9380_mem, Shared.BasisChunk009.row9381_mem, Shared.BasisChunk009.row9382_mem, Shared.BasisChunk009.row9383_mem, Shared.BasisChunk009.row9384_mem, Shared.BasisChunk009.row9385_mem, Shared.BasisChunk009.row9386_mem, Shared.BasisChunk009.row9387_mem, Shared.BasisChunk009.row9388_mem, Shared.BasisChunk009.row9389_mem, Shared.BasisChunk009.row9390_mem, Shared.BasisChunk009.row9391_mem, Shared.BasisChunk009.row9392_mem, Shared.BasisChunk009.row9393_mem, Shared.BasisChunk009.row9394_mem, Shared.BasisChunk009.row9395_mem, Shared.BasisChunk009.row9396_mem, Shared.BasisChunk009.row9398_mem, Shared.BasisChunk009.row9399_mem, Shared.BasisChunk009.row9401_mem, Shared.BasisChunk009.row9402_mem, Shared.BasisChunk009.row9404_mem, Shared.BasisChunk009.row9405_mem, Shared.BasisChunk009.row9406_mem, Shared.BasisChunk009.row9407_mem, Shared.BasisChunk009.row9408_mem, Shared.BasisChunk009.row9409_mem, Shared.BasisChunk009.row9410_mem, Shared.BasisChunk009.row9411_mem, Shared.BasisChunk009.row9413_mem, Shared.BasisChunk009.row9414_mem, Shared.BasisChunk009.row9420_mem, Shared.BasisChunk009.row9421_mem, Shared.BasisChunk009.row9422_mem, Shared.BasisChunk009.row9424_mem, Shared.BasisChunk009.row9425_mem, Shared.BasisChunk009.row9426_mem, Shared.BasisChunk009.row9427_mem, Shared.BasisChunk009.row9428_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard123
