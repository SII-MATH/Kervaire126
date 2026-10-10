import KIP126.LinProgram.Generated.Naturality.Words200.Shard097
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk036
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk037
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard097
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard097
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
  exact ⟨Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation14_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation44_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation184_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk007.relation420_zero, Shared.RelationChunk008.relation482_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk012.relation623_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk013.relation678_zero, Shared.RelationChunk013.relation682_zero, Shared.RelationChunk014.relation738_zero, Shared.RelationChunk019.relation890_zero, Shared.RelationChunk022.relation993_zero, Shared.RelationChunk032.relation1366_zero, Shared.RelationChunk035.relation1443_zero, Shared.RelationChunk036.relation1456_zero, Shared.RelationChunk036.relation1457_zero, Shared.RelationChunk036.relation1460_zero, Shared.RelationChunk036.relation1461_zero, Shared.RelationChunk037.relation1490_zero, Shared.RelationChunk037.relation1491_zero, Shared.RelationChunk037.relation1492_zero, Shared.RelationChunk037.relation1493_zero, Shared.RelationChunk037.relation1494_zero, Shared.RelationChunk037.relation1495_zero, Shared.RelationChunk037.relation1496_zero, Shared.RelationChunk037.relation1497_zero, Shared.RelationChunk037.relation1498_zero, Shared.RelationChunk037.relation1499_zero, Shared.RelationChunk037.relation1500_zero, Shared.RelationChunk037.relation1501_zero, Shared.RelationChunk037.relation1502_zero, Shared.RelationChunk037.relation1503_zero, Shared.RelationChunk037.relation1504_zero, Shared.RelationChunk037.relation1505_zero, Shared.RelationChunk037.relation1506_zero, Shared.RelationChunk037.relation1507_zero, Shared.RelationChunk037.relation1508_zero, Shared.RelationChunk037.relation1509_zero, Shared.RelationChunk037.relation1510_zero, Shared.RelationChunk037.relation1511_zero, Shared.RelationChunk037.relation1512_zero, Shared.RelationChunk037.relation1513_zero, Shared.RelationChunk037.relation1514_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12418 128 := by cbv
private def targetRows : List BasisRow := [⟨33, 183, 0, "8,1,17,1,404,1"⟩,
  ⟨33, 183, 1, "8,2,9,1,13,3,51,1"⟩,
  ⟨33, 183, 2, "8,5,13,1,80,1"⟩,
  ⟨33, 183, 3, "0,1,17,2,278,1"⟩,
  ⟨32, 183, 0, "8,1,9,1,13,6"⟩,
  ⟨32, 183, 1, "8,3,64,1,72,1"⟩,
  ⟨32, 183, 2, "8,4,23,1,101,1"⟩,
  ⟨31, 183, 0, "9,1,13,5,32,1"⟩,
  ⟨31, 183, 1, "8,3,327,1"⟩,
  ⟨31, 183, 2, "8,3,13,1,23,1,80,1"⟩,
  ⟨30, 183, 0, "8,2,17,1,255,1"⟩,
  ⟨30, 183, 1, "8,2,13,3,101,1"⟩,
  ⟨29, 183, 0, "8,1,13,4,80,1"⟩,
  ⟨29, 183, 1, "8,2,530,1"⟩,
  ⟨29, 183, 2, "0,1,64,1,260,1"⟩,
  ⟨28, 183, 0, "13,3,23,1,101,1"⟩,
  ⟨28, 183, 1, "8,3,9,1,212,1"⟩,
  ⟨28, 183, 2, "0,1,897,1"⟩,
  ⟨27, 183, 0, "921,1"⟩,
  ⟨27, 183, 1, "920,1"⟩,
  ⟨27, 183, 3, "8,2,9,1,13,1,188,1"⟩,
  ⟨26, 183, 0, "8,1,64,1,187,1"⟩,
  ⟨26, 183, 1, "8,1,9,1,13,1,267,1"⟩,
  ⟨26, 183, 2, "0,1,898,1"⟩,
  ⟨26, 183, 3, "0,15,743,1"⟩,
  ⟨25, 183, 0, "9,1,13,1,23,1,188,1"⟩,
  ⟨25, 183, 1, "8,1,64,1,188,1"⟩,
  ⟨25, 183, 2, "0,1,8,1,690,1"⟩,
  ⟨25, 183, 3, "0,7,836,1"⟩,
  ⟨24, 183, 0, "13,1,23,1,286,1"⟩,
  ⟨24, 183, 1, "8,1,704,1"⟩,
  ⟨24, 183, 2, "0,1,903,1"⟩,
  ⟨24, 183, 3, "0,1,901,1"⟩,
  ⟨23, 183, 0, "922,1"⟩,
  ⟨23, 183, 1, "13,1,23,1,287,1"⟩,
  ⟨23, 183, 2, "8,1,705,1"⟩,
  ⟨23, 183, 3, "2,1,876,1"⟩,
  ⟨22, 183, 0, "13,1,640,1"⟩,
  ⟨22, 183, 1, "2,1,877,1"⟩,
  ⟨20, 183, 1, "13,2,408,1"⟩,
  ⟨19, 183, 0, "13,2,411,1"⟩,
  ⟨19, 183, 1, "7,1,729,1"⟩,
  ⟨19, 183, 2, "0,2,891,1"⟩,
  ⟨18, 183, 0, "0,1,908,1"⟩,
  ⟨18, 183, 1, "0,1,906,1"⟩,
  ⟨18, 183, 2, "0,1,49,1,324,1"⟩,
  ⟨17, 183, 1, "0,1,50,1,324,1"⟩,
  ⟨16, 183, 0, "3,1,825,1"⟩,
  ⟨15, 183, 0, "3,2,730,1"⟩,
  ⟨15, 183, 1, "0,1,911,1"⟩,
  ⟨15, 183, 2, "0,1,3,1,815,1"⟩,
  ⟨14, 183, 1, "3,2,732,1"⟩,
  ⟨14, 183, 2, "0,1,8,3,324,1"⟩,
  ⟨14, 183, 3, "0,1,3,1,817,1"⟩,
  ⟨14, 183, 4, "0,1,3,2,719,1"⟩,
  ⟨14, 183, 5, "0,5,7,1,676,1"⟩,
  ⟨13, 183, 1, "1,2,884,1"⟩,
  ⟨13, 183, 2, "0,1,912,1"⟩,
  ⟨13, 183, 3, "0,1,43,1,392,1"⟩,
  ⟨13, 183, 4, "0,1,8,1,22,1,324,1"⟩,
  ⟨13, 183, 5, "0,2,893,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7427_mem, Shared.BasisChunk007.row7428_mem, Shared.BasisChunk007.row7429_mem, Shared.BasisChunk007.row7430_mem, Shared.BasisChunk007.row7431_mem, Shared.BasisChunk007.row7432_mem, Shared.BasisChunk007.row7433_mem, Shared.BasisChunk007.row7434_mem, Shared.BasisChunk007.row7435_mem, Shared.BasisChunk007.row7436_mem, Shared.BasisChunk007.row7437_mem, Shared.BasisChunk007.row7438_mem, Shared.BasisChunk007.row7439_mem, Shared.BasisChunk007.row7440_mem, Shared.BasisChunk007.row7441_mem, Shared.BasisChunk007.row7442_mem, Shared.BasisChunk007.row7443_mem, Shared.BasisChunk007.row7444_mem, Shared.BasisChunk007.row7445_mem, Shared.BasisChunk007.row7446_mem, Shared.BasisChunk007.row7448_mem, Shared.BasisChunk007.row7449_mem, Shared.BasisChunk007.row7450_mem, Shared.BasisChunk007.row7451_mem, Shared.BasisChunk007.row7452_mem, Shared.BasisChunk007.row7453_mem, Shared.BasisChunk007.row7454_mem, Shared.BasisChunk007.row7455_mem, Shared.BasisChunk007.row7456_mem, Shared.BasisChunk007.row7457_mem, Shared.BasisChunk007.row7458_mem, Shared.BasisChunk007.row7459_mem, Shared.BasisChunk007.row7460_mem, Shared.BasisChunk007.row7461_mem, Shared.BasisChunk007.row7462_mem, Shared.BasisChunk007.row7463_mem, Shared.BasisChunk007.row7464_mem, Shared.BasisChunk007.row7465_mem, Shared.BasisChunk007.row7466_mem, Shared.BasisChunk007.row7468_mem, Shared.BasisChunk007.row7469_mem, Shared.BasisChunk007.row7470_mem, Shared.BasisChunk007.row7471_mem, Shared.BasisChunk007.row7472_mem, Shared.BasisChunk007.row7473_mem, Shared.BasisChunk007.row7474_mem, Shared.BasisChunk007.row7476_mem, Shared.BasisChunk007.row7477_mem, Shared.BasisChunk007.row7478_mem, Shared.BasisChunk007.row7479_mem, Shared.BasisChunk007.row7480_mem, Shared.BasisChunk007.row7482_mem, Shared.BasisChunk007.row7483_mem, Shared.BasisChunk007.row7484_mem, Shared.BasisChunk007.row7485_mem, Shared.BasisChunk007.row7486_mem, Shared.BasisChunk007.row7488_mem, Shared.BasisChunk007.row7489_mem, Shared.BasisChunk007.row7490_mem, Shared.BasisChunk007.row7491_mem, Shared.BasisChunk007.row7492_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard097
