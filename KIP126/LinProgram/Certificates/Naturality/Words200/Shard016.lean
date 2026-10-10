import KIP126.LinProgram.Generated.Naturality.Words200.Shard016
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard016
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard016
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk001.relation143_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation171_zero, Shared.RelationChunk002.relation249_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk003.relation252_zero, Shared.RelationChunk003.relation254_zero, Shared.RelationChunk003.relation255_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2050 128 := by cbv
private def targetRows : List BasisRow := [⟨12, 100, 2, "0,3,19,1,69,1"⟩,
  ⟨11, 100, 0, "178,1"⟩,
  ⟨10, 100, 0, "179,1"⟩,
  ⟨9, 100, 1, "0,1,174,1"⟩,
  ⟨8, 100, 0, "22,1,69,1"⟩,
  ⟨8, 100, 1, "0,4,163,1"⟩,
  ⟨7, 100, 0, "23,1,69,1"⟩,
  ⟨6, 100, 0, "24,1,69,1"⟩,
  ⟨6, 100, 1, "1,2,163,1"⟩,
  ⟨5, 100, 1, "2,1,163,1"⟩,
  ⟨101, 101, 0, "0,101"⟩,
  ⟨34, 101, 0, "0,1,175,1"⟩,
  ⟨30, 101, 0, "0,2,8,1,116,1"⟩,
  ⟨29, 101, 0, "0,2,8,1,117,1"⟩,
  ⟨20, 101, 0, "0,2,8,2,64,1"⟩,
  ⟨19, 101, 0, "0,2,8,1,118,1"⟩,
  ⟨18, 101, 0, "0,3,167,1"⟩,
  ⟨17, 101, 0, "0,2,172,1"⟩,
  ⟨16, 101, 2, "0,3,169,1"⟩,
  ⟨15, 101, 0, "0,1,176,1"⟩,
  ⟨13, 101, 0, "1,1,21,1,69,1"⟩,
  ⟨13, 101, 1, "0,1,177,1"⟩,
  ⟨12, 101, 0, "0,1,178,1"⟩,
  ⟨11, 101, 0, "0,1,179,1"⟩,
  ⟨10, 101, 0, "0,1,8,2,69,1"⟩,
  ⟨9, 101, 1, "0,1,22,1,69,1"⟩,
  ⟨9, 101, 2, "0,5,163,1"⟩,
  ⟨8, 101, 1, "0,1,23,1,69,1"⟩,
  ⟨6, 101, 0, "0,1,2,1,163,1"⟩,
  ⟨5, 101, 0, "26,1,69,1"⟩,
  ⟨102, 102, 0, "0,102"⟩,
  ⟨35, 102, 0, "0,2,175,1"⟩,
  ⟨31, 102, 0, "183,1"⟩,
  ⟨27, 102, 0, "8,1,16,1,50,1"⟩,
  ⟨26, 102, 0, "8,1,17,1,50,1"⟩,
  ⟨25, 102, 0, "8,1,125,1"⟩,
  ⟨24, 102, 0, "8,4,16,1"⟩,
  ⟨23, 102, 0, "8,4,17,1"⟩,
  ⟨22, 102, 1, "8,2,16,1,23,1"⟩,
  ⟨21, 102, 0, "185,1"⟩,
  ⟨21, 102, 1, "8,3,42,1"⟩,
  ⟨20, 102, 0, "8,3,13,2"⟩,
  ⟨19, 102, 0, "8,2,13,1,32,1"⟩,
  ⟨19, 102, 1, "0,4,167,1"⟩,
  ⟨18, 102, 0, "8,1,13,2,23,1"⟩,
  ⟨18, 102, 2, "0,3,172,1"⟩,
  ⟨17, 102, 0, "13,2,51,1"⟩,
  ⟨17, 102, 1, "8,1,127,1"⟩,
  ⟨17, 102, 2, "0,4,169,1"⟩,
  ⟨16, 102, 0, "20,1,80,1"⟩,
  ⟨16, 102, 1, "13,2,52,1"⟩,
  ⟨16, 102, 2, "0,2,176,1"⟩,
  ⟨15, 102, 0, "186,1"⟩,
  ⟨15, 102, 1, "1,1,176,1"⟩,
  ⟨14, 102, 1, "0,2,177,1"⟩,
  ⟨13, 102, 0, "0,2,178,1"⟩,
  ⟨11, 102, 1, "0,2,8,2,69,1"⟩,
  ⟨10, 102, 1, "0,2,22,1,69,1"⟩,
  ⟨9, 102, 0, "0,2,23,1,69,1"⟩,
  ⟨7, 102, 0, "191,1"⟩,
  ⟨6, 102, 0, "0,1,26,1,69,1"⟩,
  ⟨103, 103, 0, "0,103"⟩,
  ⟨33, 103, 0, "0,1,182,1"⟩,
  ⟨32, 103, 0, "0,1,183,1"⟩,
  ⟨29, 103, 0, "0,1,8,2,71,1"⟩,
  ⟨28, 103, 0, "0,1,8,1,16,1,50,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1234_mem, Shared.BasisChunk001.row1235_mem, Shared.BasisChunk001.row1236_mem, Shared.BasisChunk001.row1238_mem, Shared.BasisChunk001.row1239_mem, Shared.BasisChunk001.row1240_mem, Shared.BasisChunk001.row1241_mem, Shared.BasisChunk001.row1242_mem, Shared.BasisChunk001.row1243_mem, Shared.BasisChunk001.row1245_mem, Shared.BasisChunk001.row1246_mem, Shared.BasisChunk001.row1247_mem, Shared.BasisChunk001.row1248_mem, Shared.BasisChunk001.row1249_mem, Shared.BasisChunk001.row1251_mem, Shared.BasisChunk001.row1252_mem, Shared.BasisChunk001.row1253_mem, Shared.BasisChunk001.row1254_mem, Shared.BasisChunk001.row1257_mem, Shared.BasisChunk001.row1258_mem, Shared.BasisChunk001.row1259_mem, Shared.BasisChunk001.row1260_mem, Shared.BasisChunk001.row1261_mem, Shared.BasisChunk001.row1262_mem, Shared.BasisChunk001.row1263_mem, Shared.BasisChunk001.row1265_mem, Shared.BasisChunk001.row1266_mem, Shared.BasisChunk001.row1268_mem, Shared.BasisChunk001.row1269_mem, Shared.BasisChunk001.row1270_mem, Shared.BasisChunk001.row1271_mem, Shared.BasisChunk001.row1272_mem, Shared.BasisChunk001.row1274_mem, Shared.BasisChunk001.row1276_mem, Shared.BasisChunk001.row1277_mem, Shared.BasisChunk001.row1278_mem, Shared.BasisChunk001.row1279_mem, Shared.BasisChunk001.row1280_mem, Shared.BasisChunk001.row1282_mem, Shared.BasisChunk001.row1283_mem, Shared.BasisChunk001.row1284_mem, Shared.BasisChunk001.row1285_mem, Shared.BasisChunk001.row1286_mem, Shared.BasisChunk001.row1287_mem, Shared.BasisChunk001.row1288_mem, Shared.BasisChunk001.row1290_mem, Shared.BasisChunk001.row1291_mem, Shared.BasisChunk001.row1292_mem, Shared.BasisChunk001.row1293_mem, Shared.BasisChunk001.row1294_mem, Shared.BasisChunk001.row1295_mem, Shared.BasisChunk001.row1296_mem, Shared.BasisChunk001.row1297_mem, Shared.BasisChunk001.row1298_mem, Shared.BasisChunk001.row1300_mem, Shared.BasisChunk001.row1301_mem, Shared.BasisChunk001.row1304_mem, Shared.BasisChunk001.row1306_mem, Shared.BasisChunk001.row1307_mem, Shared.BasisChunk001.row1309_mem, Shared.BasisChunk001.row1311_mem, Shared.BasisChunk001.row1312_mem, Shared.BasisChunk001.row1313_mem, Shared.BasisChunk001.row1314_mem, Shared.BasisChunk001.row1315_mem, Shared.BasisChunk001.row1316_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard016
