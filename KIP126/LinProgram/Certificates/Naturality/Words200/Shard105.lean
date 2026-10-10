import KIP126.LinProgram.Generated.Naturality.Words200.Shard105
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk027
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk037
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk042
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk043
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk044
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard105
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard105
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
  exact ⟨Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation134_zero, Shared.RelationChunk005.relation347_zero, Shared.RelationChunk007.relation441_zero, Shared.RelationChunk009.relation496_zero, Shared.RelationChunk009.relation497_zero, Shared.RelationChunk011.relation602_zero, Shared.RelationChunk014.relation709_zero, Shared.RelationChunk015.relation769_zero, Shared.RelationChunk015.relation770_zero, Shared.RelationChunk015.relation772_zero, Shared.RelationChunk015.relation773_zero, Shared.RelationChunk015.relation774_zero, Shared.RelationChunk015.relation775_zero, Shared.RelationChunk015.relation776_zero, Shared.RelationChunk024.relation1037_zero, Shared.RelationChunk026.relation1114_zero, Shared.RelationChunk026.relation1115_zero, Shared.RelationChunk026.relation1116_zero, Shared.RelationChunk027.relation1153_zero, Shared.RelationChunk027.relation1154_zero, Shared.RelationChunk027.relation1155_zero, Shared.RelationChunk034.relation1399_zero, Shared.RelationChunk037.relation1489_zero, Shared.RelationChunk042.relation1630_zero, Shared.RelationChunk042.relation1631_zero, Shared.RelationChunk042.relation1632_zero, Shared.RelationChunk042.relation1633_zero, Shared.RelationChunk042.relation1634_zero, Shared.RelationChunk042.relation1635_zero, Shared.RelationChunk042.relation1636_zero, Shared.RelationChunk042.relation1637_zero, Shared.RelationChunk043.relation1639_zero, Shared.RelationChunk044.relation1682_zero, Shared.RelationChunk044.relation1683_zero, Shared.RelationChunk044.relation1684_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13442 128 := by cbv
private def targetRows : List BasisRow := [⟨30, 188, 1, "8,2,9,1,346,1"⟩,
  ⟨30, 188, 2, "8,3,382,1"⟩,
  ⟨29, 188, 0, "13,4,150,1"⟩,
  ⟨29, 188, 1, "8,1,9,1,13,1,292,1"⟩,
  ⟨29, 188, 2, "8,3,383,1"⟩,
  ⟨28, 188, 1, "9,1,23,1,346,1"⟩,
  ⟨28, 188, 2, "8,4,250,1"⟩,
  ⟨27, 188, 0, "17,1,627,1"⟩,
  ⟨27, 188, 1, "8,3,384,1"⟩,
  ⟨27, 188, 3, "0,1,963,1"⟩,
  ⟨26, 188, 0, "974,1"⟩,
  ⟨26, 188, 1, "973,1"⟩,
  ⟨26, 188, 2, "8,2,9,1,13,1,209,1"⟩,
  ⟨25, 188, 1, "976,1"⟩,
  ⟨25, 188, 4, "8,1,9,1,13,1,294,1"⟩,
  ⟨24, 188, 2, "9,1,13,2,261,1"⟩,
  ⟨24, 188, 3, "8,1,64,1,209,1"⟩,
  ⟨24, 188, 4, "0,1,3,1,876,1"⟩,
  ⟨23, 188, 1, "8,1,760,1"⟩,
  ⟨23, 188, 2, "0,3,943,1"⟩,
  ⟨22, 188, 0, "980,1"⟩,
  ⟨22, 188, 1, "8,1,761,1"⟩,
  ⟨22, 188, 2, "2,1,930,1"⟩,
  ⟨22, 188, 3, "0,2,959,1"⟩,
  ⟨21, 188, 0, "981,1"⟩,
  ⟨21, 188, 1, "13,1,692,1"⟩,
  ⟨21, 188, 2, "13,1,691,1"⟩,
  ⟨21, 188, 4, "0,2,960,1"⟩,
  ⟨20, 188, 0, "983,1"⟩,
  ⟨20, 188, 2, "0,1,964,1"⟩,
  ⟨20, 188, 3, "0,3,55,1,324,1"⟩,
  ⟨19, 188, 0, "984,1"⟩,
  ⟨18, 188, 0, "986,1"⟩,
  ⟨17, 188, 0, "92,1,250,1"⟩,
  ⟨17, 188, 2, "0,1,966,1"⟩,
  ⟨17, 188, 3, "0,1,965,1"⟩,
  ⟨16, 188, 1, "16,1,17,1,324,1"⟩,
  ⟨15, 188, 2, "17,2,324,1"⟩,
  ⟨14, 188, 0, "991,1"⟩,
  ⟨14, 188, 2, "60,1,324,1"⟩,
  ⟨14, 188, 4, "2,1,935,1"⟩,
  ⟨13, 188, 1, "8,2,13,1,324,1"⟩,
  ⟨13, 188, 3, "1,2,938,1"⟩,
  ⟨13, 188, 4, "0,1,3,1,884,1"⟩,
  ⟨12, 188, 0, "18,1,615,1"⟩,
  ⟨12, 188, 1, "8,1,32,1,324,1"⟩,
  ⟨12, 188, 2, "2,1,938,1"⟩,
  ⟨12, 188, 3, "2,1,7,1,746,1"⟩,
  ⟨11, 188, 0, "993,1"⟩,
  ⟨11, 188, 1, "13,1,23,1,324,1"⟩,
  ⟨11, 188, 2, "3,1,43,1,368,1"⟩,
  ⟨10, 188, 0, "13,1,699,1"⟩,
  ⟨10, 188, 1, "13,1,24,1,324,1"⟩,
  ⟨9, 188, 0, "13,1,25,1,324,1"⟩,
  ⟨8, 188, 1, "2,1,54,1,324,1"⟩,
  ⟨7, 188, 0, "994,1"⟩,
  ⟨189, 189, 0, "0,189"⟩,
  ⟨62, 189, 0, "0,61,324,1"⟩,
  ⟨59, 189, 0, "996,1"⟩,
  ⟨56, 189, 1, "0,6,916,1"⟩,
  ⟨55, 189, 0, "8,2,579,1"⟩,
  ⟨55, 189, 1, "0,6,917,1"⟩,
  ⟨54, 189, 0, "8,1,17,1,470,1"⟩,
  ⟨53, 189, 0, "8,1,777,1"⟩,
  ⟨53, 189, 1, "0,3,952,1"⟩,
  ⟨52, 189, 0, "8,4,252,1"⟩,
  ⟨51, 189, 0, "8,4,253,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7998_mem, Shared.BasisChunk007.row7999_mem, Shared.BasisChunk007.row8000_mem, Shared.BasisChunk007.row8001_mem, Shared.BasisChunk007.row8002_mem, Shared.BasisChunk007.row8004_mem, Shared.BasisChunk007.row8005_mem, Shared.BasisChunk007.row8006_mem, Shared.BasisChunk007.row8007_mem, Shared.BasisChunk007.row8009_mem, Shared.BasisChunk007.row8010_mem, Shared.BasisChunk007.row8011_mem, Shared.BasisChunk007.row8012_mem, Shared.BasisChunk007.row8014_mem, Shared.BasisChunk007.row8017_mem, Shared.BasisChunk007.row8020_mem, Shared.BasisChunk007.row8021_mem, Shared.BasisChunk007.row8022_mem, Shared.BasisChunk007.row8024_mem, Shared.BasisChunk007.row8025_mem, Shared.BasisChunk007.row8026_mem, Shared.BasisChunk007.row8027_mem, Shared.BasisChunk007.row8028_mem, Shared.BasisChunk007.row8029_mem, Shared.BasisChunk007.row8030_mem, Shared.BasisChunk007.row8031_mem, Shared.BasisChunk007.row8032_mem, Shared.BasisChunk007.row8034_mem, Shared.BasisChunk007.row8035_mem, Shared.BasisChunk007.row8037_mem, Shared.BasisChunk007.row8038_mem, Shared.BasisChunk007.row8039_mem, Shared.BasisChunk007.row8040_mem, Shared.BasisChunk007.row8042_mem, Shared.BasisChunk007.row8044_mem, Shared.BasisChunk007.row8045_mem, Shared.BasisChunk007.row8047_mem, Shared.BasisChunk007.row8050_mem, Shared.BasisChunk007.row8051_mem, Shared.BasisChunk007.row8053_mem, Shared.BasisChunk007.row8055_mem, Shared.BasisChunk007.row8057_mem, Shared.BasisChunk007.row8059_mem, Shared.BasisChunk007.row8060_mem, Shared.BasisChunk007.row8061_mem, Shared.BasisChunk007.row8062_mem, Shared.BasisChunk007.row8063_mem, Shared.BasisChunk007.row8064_mem, Shared.BasisChunk007.row8066_mem, Shared.BasisChunk007.row8067_mem, Shared.BasisChunk007.row8068_mem, Shared.BasisChunk007.row8069_mem, Shared.BasisChunk007.row8070_mem, Shared.BasisChunk007.row8071_mem, Shared.BasisChunk007.row8073_mem, Shared.BasisChunk007.row8074_mem, Shared.BasisChunk007.row8076_mem, Shared.BasisChunk007.row8077_mem, Shared.BasisChunk007.row8079_mem, Shared.BasisChunk007.row8081_mem, Shared.BasisChunk007.row8082_mem, Shared.BasisChunk007.row8083_mem, Shared.BasisChunk007.row8084_mem, Shared.BasisChunk007.row8085_mem, Shared.BasisChunk007.row8086_mem, Shared.BasisChunk007.row8087_mem, Shared.BasisChunk007.row8088_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard105
