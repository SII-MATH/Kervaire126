module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard091
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk033
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard091
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard091
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation59_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation110_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation151_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation219_zero, Shared.RelationChunk003.relation256_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation284_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk006.relation397_zero, Shared.RelationChunk006.relation400_zero, Shared.RelationChunk006.relation405_zero, Shared.RelationChunk012.relation634_zero, Shared.RelationChunk012.relation635_zero, Shared.RelationChunk012.relation638_zero, Shared.RelationChunk020.relation934_zero, Shared.RelationChunk020.relation935_zero, Shared.RelationChunk021.relation949_zero, Shared.RelationChunk021.relation950_zero, Shared.RelationChunk021.relation951_zero, Shared.RelationChunk021.relation952_zero, Shared.RelationChunk021.relation953_zero, Shared.RelationChunk021.relation955_zero, Shared.RelationChunk021.relation956_zero, Shared.RelationChunk026.relation1129_zero, Shared.RelationChunk031.relation1318_zero, Shared.RelationChunk033.relation1371_zero, Shared.RelationChunk033.relation1372_zero, Shared.RelationChunk033.relation1373_zero, Shared.RelationChunk033.relation1374_zero, Shared.RelationChunk033.relation1375_zero, Shared.RelationChunk035.relation1435_zero, Shared.RelationChunk035.relation1436_zero, Shared.RelationChunk035.relation1437_zero, Shared.RelationChunk035.relation1438_zero, Shared.RelationChunk035.relation1439_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11650 128 := by cbv
private def targetRows : List BasisRow := [⟨18, 179, 0, "880,1"⟩,
  ⟨18, 179, 1, "0,1,3,1,763,1"⟩,
  ⟨17, 179, 1, "1,2,825,1"⟩,
  ⟨17, 179, 2, "0,1,3,1,764,1"⟩,
  ⟨16, 179, 0, "2,1,824,1"⟩,
  ⟨16, 179, 1, "0,1,43,1,336,1"⟩,
  ⟨16, 179, 2, "0,1,2,1,814,1"⟩,
  ⟨15, 179, 1, "0,2,859,1"⟩,
  ⟨15, 179, 2, "0,2,858,1"⟩,
  ⟨15, 179, 3, "0,2,43,1,333,1"⟩,
  ⟨14, 179, 0, "882,1"⟩,
  ⟨14, 179, 1, "8,1,18,1,333,1"⟩,
  ⟨14, 179, 2, "1,2,826,1"⟩,
  ⟨14, 179, 3, "0,1,3,1,769,1"⟩,
  ⟨14, 179, 4, "0,2,861,1"⟩,
  ⟨13, 179, 0, "8,1,659,1"⟩,
  ⟨13, 179, 2, "1,1,860,1"⟩,
  ⟨13, 179, 3, "0,1,869,1"⟩,
  ⟨12, 179, 0, "883,1"⟩,
  ⟨12, 179, 1, "43,1,352,1"⟩,
  ⟨12, 179, 2, "8,1,20,1,324,1"⟩,
  ⟨11, 179, 1, "45,1,324,1"⟩,
  ⟨11, 179, 2, "0,1,18,1,523,1"⟩,
  ⟨10, 179, 0, "46,1,324,1"⟩,
  ⟨10, 179, 1, "0,1,18,1,524,1"⟩,
  ⟨10, 179, 2, "0,1,7,1,676,1"⟩,
  ⟨9, 179, 0, "0,3,18,1,506,1"⟩,
  ⟨8, 179, 0, "885,1"⟩,
  ⟨7, 179, 0, "0,1,8,1,18,1,324,1"⟩,
  ⟨7, 179, 1, "0,3,849,1"⟩,
  ⟨6, 179, 0, "0,3,850,1"⟩,
  ⟨180, 180, 0, "0,180"⟩,
  ⟨59, 180, 0, "0,3,851,1"⟩,
  ⟨55, 180, 0, "16,1,554,1"⟩,
  ⟨54, 180, 0, "17,1,554,1"⟩,
  ⟨53, 180, 1, "0,52,324,1"⟩,
  ⟨52, 180, 0, "8,3,295,1"⟩,
  ⟨51, 180, 0, "8,3,296,1"⟩,
  ⟨50, 180, 0, "8,1,16,1,17,1,183,1"⟩,
  ⟨49, 180, 0, "8,2,498,1"⟩,
  ⟨48, 180, 0, "8,5,145,1"⟩,
  ⟨47, 180, 0, "8,4,16,1,111,1"⟩,
  ⟨46, 180, 1, "8,4,17,1,111,1"⟩,
  ⟨45, 180, 0, "8,1,663,1"⟩,
  ⟨45, 180, 1, "8,4,211,1"⟩,
  ⟨45, 180, 2, "0,1,871,1"⟩,
  ⟨44, 180, 0, "17,1,556,1"⟩,
  ⟨44, 180, 1, "8,7,49,1"⟩,
  ⟨43, 180, 0, "8,7,50,1"⟩,
  ⟨43, 180, 1, "0,1,872,1"⟩,
  ⟨42, 180, 1, "8,5,16,1,17,2"⟩,
  ⟨42, 180, 2, "0,6,64,1,224,1"⟩,
  ⟨41, 180, 0, "8,3,298,1"⟩,
  ⟨41, 180, 1, "8,6,88,1"⟩,
  ⟨41, 180, 2, "0,6,64,1,225,1"⟩,
  ⟨40, 180, 0, "8,2,17,1,238,1"⟩,
  ⟨40, 180, 1, "8,10"⟩,
  ⟨39, 180, 0, "8,1,17,2,185,1"⟩,
  ⟨39, 180, 1, "8,8,22,1"⟩,
  ⟨39, 180, 2, "0,6,809,1"⟩,
  ⟨39, 180, 3, "0,6,807,1"⟩,
  ⟨38, 180, 0, "8,5,146,1"⟩,
  ⟨38, 180, 1, "8,8,23,1"⟩,
  ⟨38, 180, 2, "0,7,795,1"⟩,
  ⟨37, 180, 0, "8,5,147,1"⟩,
  ⟨37, 180, 1, "8,7,51,1"⟩,
  ⟨36, 180, 1, "8,4,17,1,113,1"⟩,
  ⟨36, 180, 2, "8,6,13,3"⟩,
  ⟨35, 180, 0, "16,1,64,1,138,1"⟩,
  ⟨35, 180, 1, "8,3,17,1,162,1"⟩,
  ⟨35, 180, 2, "8,5,13,2,32,1"⟩,
  ⟨35, 180, 3, "0,1,64,1,244,1"⟩,
  ⟨35, 180, 4, "0,1,8,2,491,1"⟩,
  ⟨34, 180, 0, "8,1,664,1"⟩,
  ⟨34, 180, 1, "8,4,13,3,23,1"⟩,
  ⟨34, 180, 2, "8,6,89,1"⟩,
  ⟨34, 180, 3, "0,1,138,1,149,1"⟩,
  ⟨34, 180, 4, "0,1,16,1,17,1,260,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6969_mem, Shared.BasisChunk006.row6970_mem, Shared.BasisChunk006.row6972_mem, Shared.BasisChunk006.row6973_mem, Shared.BasisChunk006.row6974_mem, Shared.BasisChunk006.row6975_mem, Shared.BasisChunk006.row6976_mem, Shared.BasisChunk006.row6978_mem, Shared.BasisChunk006.row6979_mem, Shared.BasisChunk006.row6980_mem, Shared.BasisChunk006.row6981_mem, Shared.BasisChunk006.row6982_mem, Shared.BasisChunk006.row6983_mem, Shared.BasisChunk006.row6984_mem, Shared.BasisChunk006.row6985_mem, Shared.BasisChunk006.row6986_mem, Shared.BasisChunk006.row6988_mem, Shared.BasisChunk006.row6989_mem, Shared.BasisChunk006.row6990_mem, Shared.BasisChunk006.row6991_mem, Shared.BasisChunk006.row6992_mem, Shared.BasisChunk006.row6994_mem, Shared.BasisChunk006.row6995_mem, Shared.BasisChunk006.row6996_mem, Shared.BasisChunk006.row6997_mem, Shared.BasisChunk006.row6998_mem, Shared.BasisChunk006.row6999_mem, Shared.BasisChunk006.row7000_mem, Shared.BasisChunk006.row7001_mem, Shared.BasisChunk006.row7002_mem, Shared.BasisChunk006.row7003_mem, Shared.BasisChunk006.row7004_mem, Shared.BasisChunk006.row7005_mem, Shared.BasisChunk006.row7007_mem, Shared.BasisChunk006.row7008_mem, Shared.BasisChunk006.row7010_mem, Shared.BasisChunk006.row7011_mem, Shared.BasisChunk006.row7012_mem, Shared.BasisChunk006.row7013_mem, Shared.BasisChunk006.row7014_mem, Shared.BasisChunk006.row7015_mem, Shared.BasisChunk006.row7016_mem, Shared.BasisChunk006.row7018_mem, Shared.BasisChunk006.row7020_mem, Shared.BasisChunk006.row7021_mem, Shared.BasisChunk006.row7022_mem, Shared.BasisChunk006.row7023_mem, Shared.BasisChunk006.row7024_mem, Shared.BasisChunk006.row7025_mem, Shared.BasisChunk006.row7026_mem, Shared.BasisChunk006.row7028_mem, Shared.BasisChunk006.row7029_mem, Shared.BasisChunk006.row7030_mem, Shared.BasisChunk006.row7031_mem, Shared.BasisChunk006.row7032_mem, Shared.BasisChunk006.row7033_mem, Shared.BasisChunk006.row7034_mem, Shared.BasisChunk006.row7035_mem, Shared.BasisChunk006.row7036_mem, Shared.BasisChunk006.row7037_mem, Shared.BasisChunk006.row7038_mem, Shared.BasisChunk006.row7039_mem, Shared.BasisChunk006.row7040_mem, Shared.BasisChunk006.row7041_mem, Shared.BasisChunk006.row7042_mem, Shared.BasisChunk006.row7043_mem, Shared.BasisChunk006.row7045_mem, Shared.BasisChunk006.row7046_mem, Shared.BasisChunk006.row7047_mem, Shared.BasisChunk006.row7048_mem, Shared.BasisChunk006.row7049_mem, Shared.BasisChunk006.row7050_mem, Shared.BasisChunk006.row7051_mem, Shared.BasisChunk006.row7052_mem, Shared.BasisChunk006.row7053_mem, Shared.BasisChunk006.row7054_mem, Shared.BasisChunk006.row7055_mem, Shared.BasisChunk006.row7056_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard091
