module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard015
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard015
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
  exact ⟨Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation154_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk002.relation236_zero, Shared.RelationChunk002.relation239_zero, Shared.RelationChunk002.relation240_zero, Shared.RelationChunk002.relation241_zero, Shared.RelationChunk002.relation243_zero, Shared.RelationChunk002.relation244_zero, Shared.RelationChunk002.relation245_zero, Shared.RelationChunk002.relation246_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1922 128 := by cbv
private def targetRows : List BasisRow := [⟨4, 97, 0, "0,1,7,2,69,1"⟩,
  ⟨98, 98, 0, "0,98"⟩,
  ⟨30, 98, 0, "0,2,8,1,110,1"⟩,
  ⟨29, 98, 0, "0,2,8,1,111,1"⟩,
  ⟨22, 98, 0, "0,6,149,1"⟩,
  ⟨21, 98, 0, "0,5,154,1"⟩,
  ⟨20, 98, 0, "0,2,8,1,112,1"⟩,
  ⟨19, 98, 0, "0,2,8,1,113,1"⟩,
  ⟨19, 98, 1, "0,3,160,1"⟩,
  ⟨15, 98, 0, "167,1"⟩,
  ⟨12, 98, 1, "0,4,17,1,69,1"⟩,
  ⟨10, 98, 0, "0,1,19,1,69,1"⟩,
  ⟨9, 98, 0, "0,1,20,1,69,1"⟩,
  ⟨6, 98, 0, "0,2,163,1"⟩,
  ⟨5, 98, 1, "0,2,7,2,69,1"⟩,
  ⟨4, 98, 0, "1,1,7,2,69,1"⟩,
  ⟨99, 99, 0, "0,99"⟩,
  ⟨27, 99, 0, "8,1,117,1"⟩,
  ⟨26, 99, 0, "17,1,78,1"⟩,
  ⟨25, 99, 0, "171,1"⟩,
  ⟨24, 99, 0, "8,3,39,1"⟩,
  ⟨23, 99, 0, "8,3,40,1"⟩,
  ⟨22, 99, 0, "8,2,17,1,20,1"⟩,
  ⟨21, 99, 0, "8,2,63,1"⟩,
  ⟨20, 99, 0, "8,3,9,1,13,1"⟩,
  ⟨19, 99, 0, "8,2,9,1,32,1"⟩,
  ⟨18, 99, 0, "8,1,9,1,13,1,23,1"⟩,
  ⟨17, 99, 0, "9,1,13,1,51,1"⟩,
  ⟨17, 99, 1, "8,1,118,1"⟩,
  ⟨17, 99, 2, "0,1,166,1"⟩,
  ⟨16, 99, 0, "17,1,80,1"⟩,
  ⟨16, 99, 1, "0,1,167,1"⟩,
  ⟨15, 99, 0, "173,1"⟩,
  ⟨14, 99, 0, "13,1,101,1"⟩,
  ⟨14, 99, 1, "0,1,169,1"⟩,
  ⟨13, 99, 0, "0,5,17,1,69,1"⟩,
  ⟨11, 99, 0, "0,2,19,1,69,1"⟩,
  ⟨10, 99, 0, "0,2,20,1,69,1"⟩,
  ⟨7, 99, 0, "1,1,7,2,70,1"⟩,
  ⟨7, 99, 1, "0,3,163,1"⟩,
  ⟨6, 99, 0, "0,3,7,2,69,1"⟩,
  ⟨100, 100, 0, "0,100"⟩,
  ⟨33, 100, 0, "175,1"⟩,
  ⟨29, 100, 0, "0,1,8,1,116,1"⟩,
  ⟨28, 100, 0, "0,1,8,1,117,1"⟩,
  ⟨27, 100, 0, "0,1,17,1,78,1"⟩,
  ⟨19, 100, 0, "0,1,8,2,64,1"⟩,
  ⟨18, 100, 0, "0,1,8,1,118,1"⟩,
  ⟨18, 100, 1, "0,2,166,1"⟩,
  ⟨17, 100, 0, "0,1,17,1,80,1"⟩,
  ⟨17, 100, 1, "0,2,167,1"⟩,
  ⟨16, 100, 0, "0,1,172,1"⟩,
  ⟨15, 100, 0, "1,1,168,1"⟩,
  ⟨15, 100, 1, "0,2,169,1"⟩,
  ⟨14, 100, 1, "1,1,169,1"⟩,
  ⟨13, 100, 0, "13,1,105,1"⟩,
  ⟨12, 100, 1, "13,1,107,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1160_mem, Shared.BasisChunk001.row1161_mem, Shared.BasisChunk001.row1163_mem, Shared.BasisChunk001.row1164_mem, Shared.BasisChunk001.row1166_mem, Shared.BasisChunk001.row1167_mem, Shared.BasisChunk001.row1168_mem, Shared.BasisChunk001.row1169_mem, Shared.BasisChunk001.row1170_mem, Shared.BasisChunk001.row1172_mem, Shared.BasisChunk001.row1176_mem, Shared.BasisChunk001.row1178_mem, Shared.BasisChunk001.row1179_mem, Shared.BasisChunk001.row1180_mem, Shared.BasisChunk001.row1182_mem, Shared.BasisChunk001.row1183_mem, Shared.BasisChunk001.row1184_mem, Shared.BasisChunk001.row1186_mem, Shared.BasisChunk001.row1187_mem, Shared.BasisChunk001.row1188_mem, Shared.BasisChunk001.row1189_mem, Shared.BasisChunk001.row1190_mem, Shared.BasisChunk001.row1191_mem, Shared.BasisChunk001.row1192_mem, Shared.BasisChunk001.row1193_mem, Shared.BasisChunk001.row1194_mem, Shared.BasisChunk001.row1195_mem, Shared.BasisChunk001.row1197_mem, Shared.BasisChunk001.row1198_mem, Shared.BasisChunk001.row1199_mem, Shared.BasisChunk001.row1200_mem, Shared.BasisChunk001.row1201_mem, Shared.BasisChunk001.row1202_mem, Shared.BasisChunk001.row1204_mem, Shared.BasisChunk001.row1205_mem, Shared.BasisChunk001.row1206_mem, Shared.BasisChunk001.row1208_mem, Shared.BasisChunk001.row1209_mem, Shared.BasisChunk001.row1211_mem, Shared.BasisChunk001.row1212_mem, Shared.BasisChunk001.row1213_mem, Shared.BasisChunk001.row1214_mem, Shared.BasisChunk001.row1216_mem, Shared.BasisChunk001.row1217_mem, Shared.BasisChunk001.row1218_mem, Shared.BasisChunk001.row1219_mem, Shared.BasisChunk001.row1220_mem, Shared.BasisChunk001.row1221_mem, Shared.BasisChunk001.row1222_mem, Shared.BasisChunk001.row1223_mem, Shared.BasisChunk001.row1224_mem, Shared.BasisChunk001.row1225_mem, Shared.BasisChunk001.row1226_mem, Shared.BasisChunk001.row1227_mem, Shared.BasisChunk001.row1229_mem, Shared.BasisChunk001.row1230_mem, Shared.BasisChunk001.row1233_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard015
