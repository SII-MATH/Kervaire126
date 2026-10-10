import KIP126.LinProgram.Generated.Naturality.Words200.Shard094
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk033
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard094
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard094
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
  exact ⟨Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation75_zero, Shared.RelationChunk003.relation287_zero, Shared.RelationChunk004.relation302_zero, Shared.RelationChunk008.relation459_zero, Shared.RelationChunk014.relation754_zero, Shared.RelationChunk019.relation910_zero, Shared.RelationChunk020.relation936_zero, Shared.RelationChunk021.relation959_zero, Shared.RelationChunk021.relation962_zero, Shared.RelationChunk021.relation963_zero, Shared.RelationChunk030.relation1297_zero, Shared.RelationChunk033.relation1376_zero, Shared.RelationChunk033.relation1377_zero, Shared.RelationChunk033.relation1378_zero, Shared.RelationChunk033.relation1379_zero, Shared.RelationChunk034.relation1412_zero, Shared.RelationChunk034.relation1413_zero, Shared.RelationChunk034.relation1414_zero, Shared.RelationChunk034.relation1415_zero, Shared.RelationChunk034.relation1416_zero, Shared.RelationChunk034.relation1417_zero, Shared.RelationChunk034.relation1418_zero, Shared.RelationChunk035.relation1444_zero, Shared.RelationChunk035.relation1445_zero, Shared.RelationChunk035.relation1446_zero, Shared.RelationChunk035.relation1447_zero, Shared.RelationChunk035.relation1448_zero, Shared.RelationChunk035.relation1449_zero, Shared.RelationChunk035.relation1450_zero, Shared.RelationChunk035.relation1451_zero, Shared.RelationChunk035.relation1452_zero, Shared.RelationChunk035.relation1453_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12034 128 := by cbv
private def targetRows : List BasisRow := [⟨33, 181, 0, "0,2,64,1,246,1"⟩,
  ⟨33, 181, 1, "0,2,59,1,260,1"⟩,
  ⟨32, 181, 1, "0,3,862,1"⟩,
  ⟨30, 181, 0, "889,1"⟩,
  ⟨29, 181, 0, "890,1"⟩,
  ⟨28, 181, 0, "9,1,642,1"⟩,
  ⟨28, 181, 1, "1,1,5,1,64,1,187,1"⟩,
  ⟨26, 181, 0, "0,2,8,1,655,1"⟩,
  ⟨25, 181, 0, "13,4,133,1"⟩,
  ⟨25, 181, 1, "1,2,856,1"⟩,
  ⟨25, 181, 2, "0,2,875,1"⟩,
  ⟨25, 181, 3, "0,2,874,1"⟩,
  ⟨24, 181, 0, "13,4,134,1"⟩,
  ⟨24, 181, 1, "0,1,887,1"⟩,
  ⟨24, 181, 2, "0,5,64,1,235,1"⟩,
  ⟨24, 181, 3, "0,13,743,1"⟩,
  ⟨23, 181, 0, "0,5,837,1"⟩,
  ⟨23, 181, 1, "0,5,836,1"⟩,
  ⟨22, 181, 0, "1,1,877,1"⟩,
  ⟨22, 181, 1, "0,5,838,1"⟩,
  ⟨21, 181, 0, "2,1,857,1"⟩,
  ⟨21, 181, 1, "1,2,64,1,239,1"⟩,
  ⟨21, 181, 2, "0,2,879,1"⟩,
  ⟨21, 181, 3, "0,6,825,1"⟩,
  ⟨20, 181, 0, "13,1,618,1"⟩,
  ⟨20, 181, 1, "0,2,880,1"⟩,
  ⟨19, 181, 0, "13,1,619,1"⟩,
  ⟨19, 181, 1, "0,1,47,1,324,1"⟩,
  ⟨18, 181, 0, "13,1,620,1"⟩,
  ⟨18, 181, 1, "1,1,881,1"⟩,
  ⟨17, 181, 1, "13,2,373,1"⟩,
  ⟨16, 181, 0, "95,1,213,1"⟩,
  ⟨16, 181, 1, "13,2,376,1"⟩,
  ⟨16, 181, 2, "0,2,882,1"⟩,
  ⟨16, 181, 3, "0,2,8,1,18,1,333,1"⟩,
  ⟨15, 181, 0, "892,1"⟩,
  ⟨15, 181, 1, "0,2,8,1,659,1"⟩,
  ⟨15, 181, 2, "0,2,8,1,19,1,324,1"⟩,
  ⟨15, 181, 3, "0,3,869,1"⟩,
  ⟨14, 181, 0, "76,1,239,1"⟩,
  ⟨14, 181, 1, "0,1,3,1,788,1"⟩,
  ⟨14, 181, 2, "0,2,8,1,20,1,324,1"⟩,
  ⟨13, 181, 0, "0,1,3,1,790,1"⟩,
  ⟨13, 181, 1, "0,1,3,1,789,1"⟩,
  ⟨13, 181, 2, "0,2,884,1"⟩,
  ⟨12, 181, 1, "0,1,3,1,791,1"⟩,
  ⟨12, 181, 2, "0,3,7,1,676,1"⟩,
  ⟨11, 181, 1, "0,5,18,1,506,1"⟩,
  ⟨9, 181, 0, "0,1,7,1,698,1"⟩,
  ⟨9, 181, 1, "0,5,849,1"⟩,
  ⟨8, 181, 1, "0,1,2,1,18,1,506,1"⟩,
  ⟨8, 181, 2, "0,5,850,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7182_mem, Shared.BasisChunk007.row7183_mem, Shared.BasisChunk007.row7185_mem, Shared.BasisChunk007.row7186_mem, Shared.BasisChunk007.row7187_mem, Shared.BasisChunk007.row7188_mem, Shared.BasisChunk007.row7189_mem, Shared.BasisChunk007.row7190_mem, Shared.BasisChunk007.row7191_mem, Shared.BasisChunk007.row7192_mem, Shared.BasisChunk007.row7193_mem, Shared.BasisChunk007.row7194_mem, Shared.BasisChunk007.row7195_mem, Shared.BasisChunk007.row7196_mem, Shared.BasisChunk007.row7197_mem, Shared.BasisChunk007.row7198_mem, Shared.BasisChunk007.row7199_mem, Shared.BasisChunk007.row7200_mem, Shared.BasisChunk007.row7201_mem, Shared.BasisChunk007.row7202_mem, Shared.BasisChunk007.row7203_mem, Shared.BasisChunk007.row7204_mem, Shared.BasisChunk007.row7205_mem, Shared.BasisChunk007.row7206_mem, Shared.BasisChunk007.row7207_mem, Shared.BasisChunk007.row7208_mem, Shared.BasisChunk007.row7209_mem, Shared.BasisChunk007.row7210_mem, Shared.BasisChunk007.row7211_mem, Shared.BasisChunk007.row7212_mem, Shared.BasisChunk007.row7214_mem, Shared.BasisChunk007.row7215_mem, Shared.BasisChunk007.row7216_mem, Shared.BasisChunk007.row7217_mem, Shared.BasisChunk007.row7218_mem, Shared.BasisChunk007.row7219_mem, Shared.BasisChunk007.row7220_mem, Shared.BasisChunk007.row7221_mem, Shared.BasisChunk007.row7222_mem, Shared.BasisChunk007.row7223_mem, Shared.BasisChunk007.row7224_mem, Shared.BasisChunk007.row7225_mem, Shared.BasisChunk007.row7226_mem, Shared.BasisChunk007.row7227_mem, Shared.BasisChunk007.row7228_mem, Shared.BasisChunk007.row7230_mem, Shared.BasisChunk007.row7231_mem, Shared.BasisChunk007.row7233_mem, Shared.BasisChunk007.row7234_mem, Shared.BasisChunk007.row7235_mem, Shared.BasisChunk007.row7237_mem, Shared.BasisChunk007.row7238_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard094
