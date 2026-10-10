import KIP126.LinProgram.Generated.Naturality.Words200.Shard018
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard018
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard018
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
  exact ⟨Shared.RelationChunk003.relation262_zero, Shared.RelationChunk003.relation276_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2306 128 := by cbv
private def targetRows : List BasisRow := [⟨14, 105, 0, "0,3,188,1"⟩,
  ⟨13, 105, 0, "0,1,195,1"⟩,
  ⟨12, 105, 1, "0,5,23,1,69,1"⟩,
  ⟨11, 105, 0, "1,1,192,1"⟩,
  ⟨11, 105, 1, "0,2,8,1,9,1,69,1"⟩,
  ⟨10, 105, 0, "202,1"⟩,
  ⟨10, 105, 1, "0,2,29,1,69,1"⟩,
  ⟨9, 105, 0, "2,1,181,1"⟩,
  ⟨9, 105, 1, "0,1,197,1"⟩,
  ⟨8, 105, 0, "0,1,198,1"⟩,
  ⟨6, 105, 0, "0,1,3,1,163,1"⟩,
  ⟨5, 105, 0, "0,1,7,1,143,1"⟩,
  ⟨106, 106, 0, "0,106"⟩,
  ⟨35, 106, 0, "0,4,183,1"⟩,
  ⟨33, 106, 0, "0,1,199,1"⟩,
  ⟨32, 106, 0, "0,1,200,1"⟩,
  ⟨23, 106, 0, "0,1,8,1,137,1"⟩,
  ⟨22, 106, 0, "0,1,8,1,138,1"⟩,
  ⟨19, 106, 0, "0,1,8,2,79,1"⟩,
  ⟨18, 106, 1, "0,1,8,2,80,1"⟩,
  ⟨16, 106, 0, "0,2,30,1,69,1"⟩,
  ⟨16, 106, 1, "0,4,187,1"⟩,
  ⟨15, 106, 0, "0,4,188,1"⟩,
  ⟨14, 106, 0, "23,1,83,1"⟩,
  ⟨14, 106, 2, "0,2,195,1"⟩,
  ⟨13, 106, 1, "9,1,133,1"⟩,
  ⟨13, 106, 2, "1,1,195,1"⟩,
  ⟨13, 106, 3, "0,1,201,1"⟩,
  ⟨12, 106, 0, "2,1,188,1"⟩,
  ⟨12, 106, 1, "1,2,189,1"⟩,
  ⟨11, 106, 0, "2,1,189,1"⟩,
  ⟨11, 106, 1, "0,1,202,1"⟩,
  ⟨10, 106, 0, "0,2,197,1"⟩,
  ⟨9, 106, 1, "0,2,198,1"⟩,
  ⟨8, 106, 0, "32,1,69,1"⟩,
  ⟨8, 106, 1, "2,1,191,1"⟩,
  ⟨7, 106, 0, "204,1"⟩,
  ⟨6, 106, 1, "0,2,7,1,143,1"⟩,
  ⟨107, 107, 0, "0,107"⟩,
  ⟨36, 107, 0, "0,5,183,1"⟩,
  ⟨34, 107, 0, "0,2,199,1"⟩,
  ⟨33, 107, 0, "0,2,200,1"⟩,
  ⟨24, 107, 0, "0,2,8,1,137,1"⟩,
  ⟨23, 107, 0, "0,2,8,1,138,1"⟩,
  ⟨19, 107, 0, "0,2,8,2,80,1"⟩,
  ⟨17, 107, 0, "208,1"⟩,
  ⟨17, 107, 1, "0,5,187,1"⟩,
  ⟨16, 107, 0, "0,5,188,1"⟩,
  ⟨14, 107, 0, "0,1,31,1,69,1"⟩,
  ⟨14, 107, 1, "0,2,201,1"⟩,
  ⟨13, 107, 0, "0,1,2,1,188,1"⟩,
  ⟨10, 107, 1, "0,1,8,1,13,1,69,1"⟩,
  ⟨9, 107, 1, "0,1,32,1,69,1"⟩,
  ⟨8, 107, 0, "0,1,203,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1397_mem, Shared.BasisChunk001.row1398_mem, Shared.BasisChunk001.row1400_mem, Shared.BasisChunk001.row1401_mem, Shared.BasisChunk001.row1402_mem, Shared.BasisChunk001.row1403_mem, Shared.BasisChunk001.row1404_mem, Shared.BasisChunk001.row1405_mem, Shared.BasisChunk001.row1406_mem, Shared.BasisChunk001.row1407_mem, Shared.BasisChunk001.row1408_mem, Shared.BasisChunk001.row1409_mem, Shared.BasisChunk001.row1410_mem, Shared.BasisChunk001.row1411_mem, Shared.BasisChunk001.row1413_mem, Shared.BasisChunk001.row1414_mem, Shared.BasisChunk001.row1415_mem, Shared.BasisChunk001.row1416_mem, Shared.BasisChunk001.row1418_mem, Shared.BasisChunk001.row1420_mem, Shared.BasisChunk001.row1421_mem, Shared.BasisChunk001.row1422_mem, Shared.BasisChunk001.row1423_mem, Shared.BasisChunk001.row1424_mem, Shared.BasisChunk001.row1426_mem, Shared.BasisChunk001.row1428_mem, Shared.BasisChunk001.row1429_mem, Shared.BasisChunk001.row1430_mem, Shared.BasisChunk001.row1431_mem, Shared.BasisChunk001.row1432_mem, Shared.BasisChunk001.row1433_mem, Shared.BasisChunk001.row1434_mem, Shared.BasisChunk001.row1435_mem, Shared.BasisChunk001.row1437_mem, Shared.BasisChunk001.row1438_mem, Shared.BasisChunk001.row1439_mem, Shared.BasisChunk001.row1440_mem, Shared.BasisChunk001.row1444_mem, Shared.BasisChunk001.row1446_mem, Shared.BasisChunk001.row1447_mem, Shared.BasisChunk001.row1449_mem, Shared.BasisChunk001.row1450_mem, Shared.BasisChunk001.row1451_mem, Shared.BasisChunk001.row1452_mem, Shared.BasisChunk001.row1454_mem, Shared.BasisChunk001.row1456_mem, Shared.BasisChunk001.row1457_mem, Shared.BasisChunk001.row1458_mem, Shared.BasisChunk001.row1459_mem, Shared.BasisChunk001.row1460_mem, Shared.BasisChunk001.row1461_mem, Shared.BasisChunk001.row1463_mem, Shared.BasisChunk001.row1465_mem, Shared.BasisChunk001.row1466_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard018
