import KIP126.LinProgram.Generated.Naturality.Words200.Shard117
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk050
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk051
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard117
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard117
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
  exact ⟨Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk006.relation385_zero, Shared.RelationChunk006.relation388_zero, Shared.RelationChunk006.relation394_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk011.relation572_zero, Shared.RelationChunk011.relation573_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk011.relation579_zero, Shared.RelationChunk011.relation580_zero, Shared.RelationChunk014.relation736_zero, Shared.RelationChunk017.relation834_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk019.relation895_zero, Shared.RelationChunk019.relation896_zero, Shared.RelationChunk026.relation1138_zero, Shared.RelationChunk026.relation1140_zero, Shared.RelationChunk029.relation1249_zero, Shared.RelationChunk032.relation1330_zero, Shared.RelationChunk032.relation1331_zero, Shared.RelationChunk032.relation1332_zero, Shared.RelationChunk032.relation1333_zero, Shared.RelationChunk050.relation1792_zero, Shared.RelationChunk050.relation1793_zero, Shared.RelationChunk050.relation1794_zero, Shared.RelationChunk050.relation1795_zero, Shared.RelationChunk050.relation1796_zero, Shared.RelationChunk050.relation1798_zero, Shared.RelationChunk051.relation1799_zero, Shared.RelationChunk051.relation1802_zero, Shared.RelationChunk051.relation1803_zero, Shared.RelationChunk051.relation1804_zero, Shared.RelationChunk051.relation1805_zero, Shared.RelationChunk051.relation1806_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14978 128 := by cbv
private def targetRows : List BasisRow := [⟨34, 195, 0, "8,1,9,1,13,5,23,1"⟩,
  ⟨34, 195, 1, "8,3,471,1"⟩,
  ⟨34, 195, 2, "8,4,13,2,101,1"⟩,
  ⟨33, 195, 0, "9,1,13,5,51,1"⟩,
  ⟨33, 195, 1, "8,2,9,1,435,1"⟩,
  ⟨33, 195, 2, "8,3,13,3,80,1"⟩,
  ⟨33, 195, 3, "0,6,64,1,301,1"⟩,
  ⟨32, 195, 0, "8,2,13,2,23,1,101,1"⟩,
  ⟨32, 195, 1, "8,5,201,1"⟩,
  ⟨31, 195, 1, "8,1,13,3,23,1,80,1"⟩,
  ⟨31, 195, 2, "8,4,9,1,188,1"⟩,
  ⟨30, 195, 0, "16,1,64,1,187,1"⟩,
  ⟨30, 195, 1, "13,5,101,1"⟩,
  ⟨30, 195, 2, "8,3,9,1,267,1"⟩,
  ⟨29, 195, 0, "16,1,64,1,188,1"⟩,
  ⟨29, 195, 1, "8,2,9,1,23,1,188,1"⟩,
  ⟨29, 195, 2, "0,1,64,1,347,1"⟩,
  ⟨29, 195, 3, "0,1,8,2,627,1"⟩,
  ⟨28, 195, 1, "8,1,854,1"⟩,
  ⟨28, 195, 2, "8,1,9,1,13,2,212,1"⟩,
  ⟨28, 195, 3, "0,1,138,1,209,1"⟩,
  ⟨28, 195, 4, "0,1,17,1,690,1"⟩,
  ⟨28, 195, 5, "0,1,8,1,832,1"⟩,
  ⟨27, 195, 0, "9,1,13,3,188,1"⟩,
  ⟨27, 195, 1, "8,2,638,1"⟩,
  ⟨27, 195, 2, "0,1,1078,1"⟩,
  ⟨27, 195, 3, "0,1,23,1,627,1"⟩,
  ⟨26, 195, 0, "13,3,286,1"⟩,
  ⟨26, 195, 1, "8,2,640,1"⟩,
  ⟨26, 195, 2, "0,1,1079,1"⟩,
  ⟨26, 195, 3, "0,1,64,1,349,1"⟩,
  ⟨25, 195, 0, "13,3,287,1"⟩,
  ⟨25, 195, 1, "8,1,80,1,212,1"⟩,
  ⟨25, 195, 2, "0,1,1081,1"⟩,
  ⟨25, 195, 3, "0,2,1063,1"⟩,
  ⟨24, 195, 0, "13,1,80,1,188,1"⟩,
  ⟨24, 195, 3, "0,1,1082,1"⟩,
  ⟨24, 195, 4, "0,3,1051,1"⟩,
  ⟨23, 195, 0, "3,2,877,1"⟩,
  ⟨23, 195, 1, "0,1,1084,1"⟩,
  ⟨23, 195, 2, "0,1,1083,1"⟩,
  ⟨22, 195, 0, "13,3,288,1"⟩,
  ⟨22, 195, 1, "1,1,7,1,857,1"⟩,
  ⟨22, 195, 2, "0,1,71,1,324,1"⟩,
  ⟨22, 195, 3, "0,2,1064,1"⟩,
  ⟨21, 195, 0, "13,2,532,1"⟩,
  ⟨21, 195, 2, "0,1,3,1,960,1"⟩,
  ⟨21, 195, 3, "0,7,59,1,324,1"⟩,
  ⟨20, 195, 0, "1,1,1066,1"⟩,
  ⟨20, 195, 1, "0,2,1068,1"⟩,
  ⟨19, 195, 0, "0,1,1086,1"⟩,
  ⟨19, 195, 1, "0,1,67,1,336,1"⟩,
  ⟨18, 195, 1, "0,1,8,2,16,1,324,1"⟩,
  ⟨18, 195, 2, "0,2,1069,1"⟩,
  ⟨17, 195, 1, "3,1,965,1"⟩,
  ⟨17, 195, 3, "0,1,8,2,17,1,324,1"⟩,
  ⟨17, 195, 4, "0,3,1055,1"⟩,
  ⟨16, 195, 0, "1,1,1072,1"⟩,
  ⟨16, 195, 1, "0,1,1088,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8913_mem, Shared.BasisChunk008.row8914_mem, Shared.BasisChunk008.row8915_mem, Shared.BasisChunk008.row8916_mem, Shared.BasisChunk008.row8917_mem, Shared.BasisChunk008.row8918_mem, Shared.BasisChunk008.row8919_mem, Shared.BasisChunk008.row8920_mem, Shared.BasisChunk008.row8921_mem, Shared.BasisChunk008.row8923_mem, Shared.BasisChunk008.row8924_mem, Shared.BasisChunk008.row8925_mem, Shared.BasisChunk008.row8926_mem, Shared.BasisChunk008.row8927_mem, Shared.BasisChunk008.row8928_mem, Shared.BasisChunk008.row8929_mem, Shared.BasisChunk008.row8930_mem, Shared.BasisChunk008.row8931_mem, Shared.BasisChunk008.row8933_mem, Shared.BasisChunk008.row8934_mem, Shared.BasisChunk008.row8935_mem, Shared.BasisChunk008.row8936_mem, Shared.BasisChunk008.row8937_mem, Shared.BasisChunk008.row8938_mem, Shared.BasisChunk008.row8939_mem, Shared.BasisChunk008.row8940_mem, Shared.BasisChunk008.row8941_mem, Shared.BasisChunk008.row8942_mem, Shared.BasisChunk008.row8943_mem, Shared.BasisChunk008.row8944_mem, Shared.BasisChunk008.row8945_mem, Shared.BasisChunk008.row8946_mem, Shared.BasisChunk008.row8947_mem, Shared.BasisChunk008.row8948_mem, Shared.BasisChunk008.row8949_mem, Shared.BasisChunk008.row8950_mem, Shared.BasisChunk008.row8953_mem, Shared.BasisChunk008.row8954_mem, Shared.BasisChunk008.row8955_mem, Shared.BasisChunk008.row8956_mem, Shared.BasisChunk008.row8957_mem, Shared.BasisChunk008.row8958_mem, Shared.BasisChunk008.row8959_mem, Shared.BasisChunk008.row8960_mem, Shared.BasisChunk008.row8961_mem, Shared.BasisChunk008.row8962_mem, Shared.BasisChunk008.row8964_mem, Shared.BasisChunk008.row8965_mem, Shared.BasisChunk008.row8966_mem, Shared.BasisChunk008.row8967_mem, Shared.BasisChunk008.row8968_mem, Shared.BasisChunk008.row8969_mem, Shared.BasisChunk008.row8971_mem, Shared.BasisChunk008.row8972_mem, Shared.BasisChunk008.row8974_mem, Shared.BasisChunk008.row8976_mem, Shared.BasisChunk008.row8977_mem, Shared.BasisChunk008.row8978_mem, Shared.BasisChunk008.row8979_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard117
