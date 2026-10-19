module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard017
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard017
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation38_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation185_zero, Shared.RelationChunk001.relation186_zero, Shared.RelationChunk003.relation256_zero, Shared.RelationChunk003.relation257_zero, Shared.RelationChunk003.relation258_zero, Shared.RelationChunk003.relation268_zero, Shared.RelationChunk003.relation269_zero, Shared.RelationChunk003.relation270_zero, Shared.RelationChunk003.relation272_zero, Shared.RelationChunk003.relation274_zero, Shared.RelationChunk003.relation275_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2178 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 103, 0, "0,1,184,1"⟩,
  ⟨22, 103, 0, "0,1,185,1"⟩,
  ⟨20, 103, 0, "0,5,167,1"⟩,
  ⟨19, 103, 0, "0,1,8,2,72,1"⟩,
  ⟨19, 103, 1, "0,4,172,1"⟩,
  ⟨18, 103, 0, "0,1,8,1,127,1"⟩,
  ⟨18, 103, 1, "0,5,169,1"⟩,
  ⟨17, 103, 0, "0,1,20,1,80,1"⟩,
  ⟨17, 103, 1, "0,3,176,1"⟩,
  ⟨13, 103, 0, "0,1,187,1"⟩,
  ⟨12, 103, 0, "23,1,75,1"⟩,
  ⟨12, 103, 1, "0,1,188,1"⟩,
  ⟨11, 103, 0, "23,1,76,1"⟩,
  ⟨11, 103, 1, "0,1,189,1"⟩,
  ⟨10, 103, 1, "1,2,174,1"⟩,
  ⟨10, 103, 2, "0,3,23,1,69,1"⟩,
  ⟨9, 103, 1, "1,1,181,1"⟩,
  ⟨9, 103, 2, "0,1,190,1"⟩,
  ⟨8, 103, 0, "29,1,69,1"⟩,
  ⟨8, 103, 1, "0,1,191,1"⟩,
  ⟨104, 104, 0, "0,104"⟩,
  ⟨34, 104, 0, "0,2,182,1"⟩,
  ⟨33, 104, 1, "0,2,183,1"⟩,
  ⟨30, 104, 0, "0,2,8,2,71,1"⟩,
  ⟨29, 104, 0, "0,2,8,1,16,1,50,1"⟩,
  ⟨24, 104, 0, "0,2,184,1"⟩,
  ⟨23, 104, 0, "0,2,185,1"⟩,
  ⟨20, 104, 0, "0,5,172,1"⟩,
  ⟨19, 104, 0, "0,2,8,1,127,1"⟩,
  ⟨16, 104, 0, "194,1"⟩,
  ⟨14, 104, 0, "30,1,69,1"⟩,
  ⟨14, 104, 1, "0,2,187,1"⟩,
  ⟨13, 104, 1, "0,2,188,1"⟩,
  ⟨12, 104, 1, "0,2,189,1"⟩,
  ⟨11, 104, 1, "0,4,23,1,69,1"⟩,
  ⟨10, 104, 0, "196,1"⟩,
  ⟨10, 104, 1, "0,1,8,1,9,1,69,1"⟩,
  ⟨10, 104, 2, "0,2,190,1"⟩,
  ⟨9, 104, 1, "0,1,29,1,69,1"⟩,
  ⟨8, 104, 1, "1,1,28,1,69,1"⟩,
  ⟨7, 104, 0, "198,1"⟩,
  ⟨7, 104, 1, "2,1,24,1,69,1"⟩,
  ⟨6, 104, 0, "2,1,25,1,69,1"⟩,
  ⟨4, 104, 0, "7,1,143,1"⟩,
  ⟨105, 105, 0, "0,105"⟩,
  ⟨34, 105, 0, "0,3,183,1"⟩,
  ⟨31, 105, 0, "200,1"⟩,
  ⟨28, 105, 0, "8,2,77,1"⟩,
  ⟨27, 105, 0, "8,2,78,1"⟩,
  ⟨26, 105, 0, "8,1,17,1,56,1"⟩,
  ⟨25, 105, 0, "8,1,136,1"⟩,
  ⟨25, 105, 1, "0,3,184,1"⟩,
  ⟨24, 105, 0, "8,4,19,1"⟩,
  ⟨23, 105, 0, "8,4,20,1"⟩,
  ⟨22, 105, 1, "8,3,45,1"⟩,
  ⟨21, 105, 0, "8,1,138,1"⟩,
  ⟨21, 105, 1, "8,3,46,1"⟩,
  ⟨20, 105, 0, "8,2,9,1,13,2"⟩,
  ⟨19, 105, 0, "8,1,9,1,13,1,32,1"⟩,
  ⟨18, 105, 0, "9,1,13,2,23,1"⟩,
  ⟨17, 105, 0, "8,2,80,1"⟩,
  ⟨16, 105, 0, "22,1,80,1"⟩,
  ⟨15, 105, 0, "23,1,80,1"⟩,
  ⟨15, 105, 1, "0,1,30,1,69,1"⟩,
  ⟨15, 105, 2, "0,3,187,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1318_mem, Shared.BasisChunk001.row1319_mem, Shared.BasisChunk001.row1320_mem, Shared.BasisChunk001.row1321_mem, Shared.BasisChunk001.row1322_mem, Shared.BasisChunk001.row1323_mem, Shared.BasisChunk001.row1324_mem, Shared.BasisChunk001.row1325_mem, Shared.BasisChunk001.row1326_mem, Shared.BasisChunk001.row1327_mem, Shared.BasisChunk001.row1328_mem, Shared.BasisChunk001.row1329_mem, Shared.BasisChunk001.row1330_mem, Shared.BasisChunk001.row1331_mem, Shared.BasisChunk001.row1333_mem, Shared.BasisChunk001.row1334_mem, Shared.BasisChunk001.row1336_mem, Shared.BasisChunk001.row1337_mem, Shared.BasisChunk001.row1338_mem, Shared.BasisChunk001.row1339_mem, Shared.BasisChunk001.row1340_mem, Shared.BasisChunk001.row1341_mem, Shared.BasisChunk001.row1343_mem, Shared.BasisChunk001.row1344_mem, Shared.BasisChunk001.row1345_mem, Shared.BasisChunk001.row1346_mem, Shared.BasisChunk001.row1347_mem, Shared.BasisChunk001.row1348_mem, Shared.BasisChunk001.row1349_mem, Shared.BasisChunk001.row1351_mem, Shared.BasisChunk001.row1353_mem, Shared.BasisChunk001.row1354_mem, Shared.BasisChunk001.row1356_mem, Shared.BasisChunk001.row1358_mem, Shared.BasisChunk001.row1360_mem, Shared.BasisChunk001.row1361_mem, Shared.BasisChunk001.row1362_mem, Shared.BasisChunk001.row1363_mem, Shared.BasisChunk001.row1365_mem, Shared.BasisChunk001.row1367_mem, Shared.BasisChunk001.row1368_mem, Shared.BasisChunk001.row1369_mem, Shared.BasisChunk001.row1370_mem, Shared.BasisChunk001.row1372_mem, Shared.BasisChunk001.row1373_mem, Shared.BasisChunk001.row1374_mem, Shared.BasisChunk001.row1376_mem, Shared.BasisChunk001.row1377_mem, Shared.BasisChunk001.row1378_mem, Shared.BasisChunk001.row1379_mem, Shared.BasisChunk001.row1380_mem, Shared.BasisChunk001.row1381_mem, Shared.BasisChunk001.row1382_mem, Shared.BasisChunk001.row1383_mem, Shared.BasisChunk001.row1385_mem, Shared.BasisChunk001.row1386_mem, Shared.BasisChunk001.row1387_mem, Shared.BasisChunk001.row1388_mem, Shared.BasisChunk001.row1389_mem, Shared.BasisChunk001.row1390_mem, Shared.BasisChunk001.row1392_mem, Shared.BasisChunk001.row1393_mem, Shared.BasisChunk001.row1394_mem, Shared.BasisChunk001.row1395_mem, Shared.BasisChunk001.row1396_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard017
