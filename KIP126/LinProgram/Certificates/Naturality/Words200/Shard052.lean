import KIP126.LinProgram.Generated.Naturality.Words200.Shard052
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard052
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard052
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
  exact ⟨Shared.RelationChunk001.relation176_zero, Shared.RelationChunk001.relation177_zero, Shared.RelationChunk001.relation178_zero, Shared.RelationChunk001.relation179_zero, Shared.RelationChunk004.relation320_zero, Shared.RelationChunk006.relation392_zero, Shared.RelationChunk006.relation393_zero, Shared.RelationChunk012.relation649_zero, Shared.RelationChunk013.relation689_zero, Shared.RelationChunk014.relation727_zero, Shared.RelationChunk014.relation733_zero, Shared.RelationChunk014.relation734_zero, Shared.RelationChunk014.relation735_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6658 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 150, 3, "0,22,324,1"⟩,
  ⟨22, 150, 0, "8,1,17,1,188,1"⟩,
  ⟨22, 150, 1, "0,1,13,1,292,1"⟩,
  ⟨21, 150, 1, "17,1,267,1"⟩,
  ⟨21, 150, 2, "0,1,551,1"⟩,
  ⟨20, 150, 0, "13,1,303,1"⟩,
  ⟨20, 150, 1, "8,1,13,1,212,1"⟩,
  ⟨20, 150, 2, "0,2,539,1"⟩,
  ⟨19, 150, 0, "13,2,188,1"⟩,
  ⟨19, 150, 1, "9,1,328,1"⟩,
  ⟨18, 150, 1, "13,2,189,1"⟩,
  ⟨16, 150, 0, "13,2,190,1"⟩,
  ⟨16, 150, 1, "0,2,8,1,337,1"⟩,
  ⟨16, 150, 2, "0,3,533,1"⟩,
  ⟨15, 150, 0, "9,1,331,1"⟩,
  ⟨15, 150, 2, "0,2,540,1"⟩,
  ⟨13, 150, 2, "0,1,7,1,371,1"⟩,
  ⟨13, 150, 3, "0,2,543,1"⟩,
  ⟨12, 150, 0, "8,1,367,1"⟩,
  ⟨12, 150, 3, "0,2,544,1"⟩,
  ⟨12, 150, 4, "0,2,7,1,366,1"⟩,
  ⟨11, 150, 0, "562,1"⟩,
  ⟨11, 150, 1, "43,1,191,1"⟩,
  ⟨11, 150, 2, "2,1,521,1"⟩,
  ⟨11, 150, 3, "1,1,544,1"⟩,
  ⟨11, 150, 4, "0,2,7,1,367,1"⟩,
  ⟨10, 150, 0, "564,1"⟩,
  ⟨10, 150, 1, "563,1"⟩,
  ⟨10, 150, 2, "2,1,523,1"⟩,
  ⟨10, 150, 3, "1,1,545,1"⟩,
  ⟨10, 150, 4, "0,1,3,1,480,1"⟩,
  ⟨10, 150, 5, "0,2,546,1"⟩,
  ⟨9, 150, 0, "565,1"⟩,
  ⟨9, 150, 1, "7,1,394,1"⟩,
  ⟨9, 150, 2, "3,2,396,1"⟩,
  ⟨9, 150, 3, "2,1,524,1"⟩,
  ⟨9, 150, 4, "1,1,547,1"⟩,
  ⟨9, 150, 6, "0,4,526,1"⟩,
  ⟨8, 150, 2, "7,1,396,1"⟩,
  ⟨8, 150, 3, "3,2,398,1"⟩,
  ⟨8, 150, 4, "2,1,525,1"⟩,
  ⟨8, 150, 6, "0,6,7,1,324,1"⟩,
  ⟨7, 150, 0, "7,1,398,1"⟩,
  ⟨7, 150, 1, "3,2,400,1"⟩,
  ⟨7, 150, 3, "0,1,9,1,69,2"⟩,
  ⟨7, 150, 4, "0,1,7,1,378,1"⟩,
  ⟨6, 150, 0, "7,1,400,1"⟩,
  ⟨6, 150, 1, "2,1,526,1"⟩,
  ⟨6, 150, 2, "0,1,9,1,324,1"⟩,
  ⟨6, 150, 3, "0,2,548,1"⟩,
  ⟨5, 150, 0, "10,1,324,1"⟩,
  ⟨5, 150, 1, "2,1,527,1"⟩,
  ⟨5, 150, 2, "0,2,2,1,7,1,324,1"⟩,
  ⟨4, 150, 0, "11,1,324,1"⟩,
  ⟨151, 151, 0, "0,151"⟩,
  ⟨49, 151, 0, "0,1,553,1"⟩,
  ⟨48, 151, 0, "0,1,554,1"⟩,
  ⟨45, 151, 0, "0,1,8,2,236,1"⟩,
  ⟨44, 151, 0, "0,1,8,1,16,1,183,1"⟩,
  ⟨39, 151, 0, "0,1,555,1"⟩,
  ⟨38, 151, 0, "0,1,556,1"⟩,
  ⟨36, 151, 0, "0,5,17,1,244,1"⟩,
  ⟨35, 151, 0, "0,1,8,2,237,1"⟩,
  ⟨35, 151, 1, "0,4,17,2,138,1"⟩,
  ⟨34, 151, 0, "0,1,8,2,238,1"⟩,
  ⟨34, 151, 1, "0,8,491,1"⟩,
  ⟨33, 151, 0, "0,1,8,1,17,1,185,1"⟩,
  ⟨33, 151, 1, "0,6,509,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row4003_mem, Shared.BasisChunk003.row4004_mem, Shared.BasisChunk003.row4005_mem, Shared.BasisChunk003.row4007_mem, Shared.BasisChunk003.row4008_mem, Shared.BasisChunk003.row4009_mem, Shared.BasisChunk003.row4010_mem, Shared.BasisChunk003.row4011_mem, Shared.BasisChunk003.row4012_mem, Shared.BasisChunk003.row4013_mem, Shared.BasisChunk003.row4015_mem, Shared.BasisChunk003.row4017_mem, Shared.BasisChunk003.row4018_mem, Shared.BasisChunk003.row4019_mem, Shared.BasisChunk003.row4020_mem, Shared.BasisChunk003.row4022_mem, Shared.BasisChunk003.row4027_mem, Shared.BasisChunk003.row4028_mem, Shared.BasisChunk003.row4029_mem, Shared.BasisChunk003.row4032_mem, Shared.BasisChunk003.row4033_mem, Shared.BasisChunk003.row4034_mem, Shared.BasisChunk003.row4035_mem, Shared.BasisChunk003.row4036_mem, Shared.BasisChunk003.row4037_mem, Shared.BasisChunk003.row4038_mem, Shared.BasisChunk003.row4039_mem, Shared.BasisChunk003.row4040_mem, Shared.BasisChunk003.row4041_mem, Shared.BasisChunk003.row4042_mem, Shared.BasisChunk003.row4043_mem, Shared.BasisChunk003.row4044_mem, Shared.BasisChunk003.row4045_mem, Shared.BasisChunk003.row4046_mem, Shared.BasisChunk003.row4047_mem, Shared.BasisChunk003.row4048_mem, Shared.BasisChunk003.row4049_mem, Shared.BasisChunk003.row4051_mem, Shared.BasisChunk003.row4054_mem, Shared.BasisChunk003.row4055_mem, Shared.BasisChunk003.row4056_mem, Shared.BasisChunk003.row4058_mem, Shared.BasisChunk003.row4059_mem, Shared.BasisChunk003.row4060_mem, Shared.BasisChunk003.row4062_mem, Shared.BasisChunk003.row4063_mem, Shared.BasisChunk003.row4064_mem, Shared.BasisChunk003.row4065_mem, Shared.BasisChunk003.row4066_mem, Shared.BasisChunk003.row4067_mem, Shared.BasisChunk003.row4068_mem, Shared.BasisChunk003.row4069_mem, Shared.BasisChunk003.row4070_mem, Shared.BasisChunk003.row4071_mem, Shared.BasisChunk003.row4072_mem, Shared.BasisChunk003.row4073_mem, Shared.BasisChunk003.row4074_mem, Shared.BasisChunk003.row4075_mem, Shared.BasisChunk003.row4076_mem, Shared.BasisChunk003.row4078_mem, Shared.BasisChunk003.row4079_mem, Shared.BasisChunk003.row4080_mem, Shared.BasisChunk003.row4081_mem, Shared.BasisChunk003.row4082_mem, Shared.BasisChunk003.row4083_mem, Shared.BasisChunk003.row4084_mem, Shared.BasisChunk003.row4085_mem, Shared.BasisChunk003.row4086_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard052
