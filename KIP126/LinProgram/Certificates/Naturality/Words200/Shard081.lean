import KIP126.LinProgram.Generated.Naturality.Words200.Shard081
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard081
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard081
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
  exact ⟨Shared.RelationChunk000.relation3_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk002.relation248_zero, Shared.RelationChunk003.relation286_zero, Shared.RelationChunk008.relation481_zero, Shared.RelationChunk009.relation509_zero, Shared.RelationChunk009.relation510_zero, Shared.RelationChunk009.relation511_zero, Shared.RelationChunk009.relation512_zero, Shared.RelationChunk009.relation513_zero, Shared.RelationChunk009.relation514_zero, Shared.RelationChunk009.relation515_zero, Shared.RelationChunk009.relation516_zero, Shared.RelationChunk014.relation714_zero, Shared.RelationChunk014.relation715_zero, Shared.RelationChunk014.relation716_zero, Shared.RelationChunk014.relation718_zero, Shared.RelationChunk015.relation780_zero, Shared.RelationChunk017.relation813_zero, Shared.RelationChunk017.relation814_zero, Shared.RelationChunk017.relation815_zero, Shared.RelationChunk017.relation816_zero, Shared.RelationChunk017.relation817_zero, Shared.RelationChunk017.relation818_zero, Shared.RelationChunk017.relation819_zero, Shared.RelationChunk017.relation820_zero, Shared.RelationChunk017.relation821_zero, Shared.RelationChunk017.relation822_zero, Shared.RelationChunk017.relation823_zero, Shared.RelationChunk028.relation1178_zero, Shared.RelationChunk028.relation1179_zero, Shared.RelationChunk028.relation1180_zero, Shared.RelationChunk028.relation1181_zero, Shared.RelationChunk028.relation1182_zero, Shared.RelationChunk028.relation1184_zero, Shared.RelationChunk028.relation1185_zero, Shared.RelationChunk028.relation1186_zero, Shared.RelationChunk028.relation1187_zero, Shared.RelationChunk028.relation1188_zero, Shared.RelationChunk028.relation1189_zero, Shared.RelationChunk028.relation1190_zero, Shared.RelationChunk028.relation1191_zero, Shared.RelationChunk028.relation1192_zero, Shared.RelationChunk028.relation1193_zero, Shared.RelationChunk028.relation1194_zero, Shared.RelationChunk028.relation1195_zero, Shared.RelationChunk028.relation1196_zero, Shared.RelationChunk028.relation1197_zero, Shared.RelationChunk028.relation1198_zero, Shared.RelationChunk028.relation1199_zero, Shared.RelationChunk028.relation1203_zero, Shared.RelationChunk028.relation1204_zero, Shared.RelationChunk028.relation1205_zero, Shared.RelationChunk028.relation1206_zero, Shared.RelationChunk028.relation1207_zero, Shared.RelationChunk028.relation1208_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10370 128 := by cbv
private def targetRows : List BasisRow := [⟨5, 172, 1, "1,2,3,1,18,1,324,1"⟩,
  ⟨4, 172, 0, "38,1,324,1"⟩,
  ⟨173, 173, 0, "0,173"⟩,
  ⟨58, 173, 0, "0,1,783,1"⟩,
  ⟨54, 173, 0, "0,2,8,1,578,1"⟩,
  ⟨53, 173, 0, "0,2,8,1,579,1"⟩,
  ⟨47, 173, 1, "0,9,686,1"⟩,
  ⟨46, 173, 0, "0,45,324,1"⟩,
  ⟨44, 173, 0, "0,2,8,2,402,1"⟩,
  ⟨43, 173, 0, "0,2,8,2,403,1"⟩,
  ⟨42, 173, 0, "0,3,17,1,452,1"⟩,
  ⟨41, 173, 0, "0,2,17,2,225,1"⟩,
  ⟨40, 173, 2, "0,6,725,1"⟩,
  ⟨39, 173, 0, "17,1,488,1"⟩,
  ⟨39, 173, 1, "0,4,752,1"⟩,
  ⟨38, 173, 0, "8,1,596,1"⟩,
  ⟨37, 173, 0, "8,1,597,1"⟩,
  ⟨37, 173, 1, "0,3,759,1"⟩,
  ⟨36, 173, 0, "8,3,257,1"⟩,
  ⟨35, 173, 0, "8,2,17,1,206,1"⟩,
  ⟨34, 173, 1, "8,3,258,1"⟩,
  ⟨33, 173, 0, "17,1,491,1"⟩,
  ⟨33, 173, 1, "8,3,259,1"⟩,
  ⟨32, 173, 0, "8,4,180,1"⟩,
  ⟨31, 173, 0, "796,1"⟩,
  ⟨31, 173, 2, "8,3,9,1,167,1"⟩,
  ⟨30, 173, 0, "8,1,64,1,149,1"⟩,
  ⟨30, 173, 1, "8,2,9,1,248,1"⟩,
  ⟨30, 173, 2, "8,3,260,1"⟩,
  ⟨29, 173, 0, "8,1,598,1"⟩,
  ⟨29, 173, 1, "8,1,16,1,292,1"⟩,
  ⟨29, 173, 2, "8,1,9,1,13,1,219,1"⟩,
  ⟨28, 173, 0, "9,1,13,2,194,1"⟩,
  ⟨28, 173, 1, "8,1,599,1"⟩,
  ⟨28, 173, 2, "8,1,17,1,292,1"⟩,
  ⟨27, 173, 0, "8,1,602,1"⟩,
  ⟨27, 173, 1, "8,2,420,1"⟩,
  ⟨26, 173, 0, "8,1,13,1,346,1"⟩,
  ⟨26, 173, 1, "8,2,16,1,209,1"⟩,
  ⟨25, 173, 0, "13,2,292,1"⟩,
  ⟨25, 173, 1, "8,2,17,1,209,1"⟩,
  ⟨24, 173, 1, "8,3,261,1"⟩,
  ⟨23, 173, 0, "8,2,423,1"⟩,
  ⟨23, 173, 1, "0,1,8,1,69,1,147,1"⟩,
  ⟨23, 173, 2, "0,3,64,1,209,1"⟩,
  ⟨22, 173, 0, "8,1,13,2,209,1"⟩,
  ⟨22, 173, 1, "0,2,17,1,475,1"⟩,
  ⟨22, 173, 2, "0,3,760,1"⟩,
  ⟨21, 173, 0, "13,2,294,1"⟩,
  ⟨21, 173, 1, "0,2,780,1"⟩,
  ⟨20, 173, 1, "13,3,181,1"⟩,
  ⟨20, 173, 2, "0,3,762,1"⟩,
  ⟨19, 173, 1, "0,3,763,1"⟩,
  ⟨18, 173, 0, "0,6,732,1"⟩,
  ⟨17, 173, 1, "1,1,781,1"⟩,
  ⟨16, 173, 0, "1,1,3,1,680,1"⟩,
  ⟨16, 173, 1, "0,5,743,1"⟩,
  ⟨15, 173, 0, "799,1"⟩,
  ⟨15, 173, 1, "3,1,709,1"⟩,
  ⟨15, 173, 2, "0,13,18,1,324,1"⟩,
  ⟨14, 173, 0, "800,1"⟩,
  ⟨14, 173, 2, "0,1,787,1"⟩,
  ⟨13, 173, 0, "801,1"⟩,
  ⟨13, 173, 1, "40,1,69,2"⟩,
  ⟨13, 173, 3, "13,1,69,1,134,1"⟩,
  ⟨13, 173, 4, "0,1,788,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6192_mem, Shared.BasisChunk006.row6193_mem, Shared.BasisChunk006.row6194_mem, Shared.BasisChunk006.row6195_mem, Shared.BasisChunk006.row6196_mem, Shared.BasisChunk006.row6197_mem, Shared.BasisChunk006.row6199_mem, Shared.BasisChunk006.row6200_mem, Shared.BasisChunk006.row6201_mem, Shared.BasisChunk006.row6202_mem, Shared.BasisChunk006.row6203_mem, Shared.BasisChunk006.row6204_mem, Shared.BasisChunk006.row6207_mem, Shared.BasisChunk006.row6208_mem, Shared.BasisChunk006.row6209_mem, Shared.BasisChunk006.row6210_mem, Shared.BasisChunk006.row6211_mem, Shared.BasisChunk006.row6212_mem, Shared.BasisChunk006.row6213_mem, Shared.BasisChunk006.row6214_mem, Shared.BasisChunk006.row6216_mem, Shared.BasisChunk006.row6217_mem, Shared.BasisChunk006.row6218_mem, Shared.BasisChunk006.row6219_mem, Shared.BasisChunk006.row6220_mem, Shared.BasisChunk006.row6222_mem, Shared.BasisChunk006.row6223_mem, Shared.BasisChunk006.row6224_mem, Shared.BasisChunk006.row6225_mem, Shared.BasisChunk006.row6226_mem, Shared.BasisChunk006.row6227_mem, Shared.BasisChunk006.row6228_mem, Shared.BasisChunk006.row6229_mem, Shared.BasisChunk006.row6230_mem, Shared.BasisChunk006.row6231_mem, Shared.BasisChunk006.row6232_mem, Shared.BasisChunk006.row6233_mem, Shared.BasisChunk006.row6234_mem, Shared.BasisChunk006.row6235_mem, Shared.BasisChunk006.row6236_mem, Shared.BasisChunk006.row6237_mem, Shared.BasisChunk006.row6239_mem, Shared.BasisChunk006.row6241_mem, Shared.BasisChunk006.row6242_mem, Shared.BasisChunk006.row6243_mem, Shared.BasisChunk006.row6244_mem, Shared.BasisChunk006.row6245_mem, Shared.BasisChunk006.row6246_mem, Shared.BasisChunk006.row6247_mem, Shared.BasisChunk006.row6248_mem, Shared.BasisChunk006.row6250_mem, Shared.BasisChunk006.row6251_mem, Shared.BasisChunk006.row6253_mem, Shared.BasisChunk006.row6254_mem, Shared.BasisChunk006.row6256_mem, Shared.BasisChunk006.row6257_mem, Shared.BasisChunk006.row6258_mem, Shared.BasisChunk006.row6259_mem, Shared.BasisChunk006.row6260_mem, Shared.BasisChunk006.row6261_mem, Shared.BasisChunk006.row6262_mem, Shared.BasisChunk006.row6264_mem, Shared.BasisChunk006.row6265_mem, Shared.BasisChunk006.row6266_mem, Shared.BasisChunk006.row6268_mem, Shared.BasisChunk006.row6269_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard081
