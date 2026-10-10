import KIP126.LinProgram.Generated.Naturality.Words200.Shard012
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard012
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard012
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
  exact ⟨Shared.RelationChunk000.relation16_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk001.relation188_zero, Shared.RelationChunk001.relation189_zero, Shared.RelationChunk001.relation191_zero, Shared.RelationChunk001.relation192_zero, Shared.RelationChunk001.relation193_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk001.relation198_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation200_zero, Shared.RelationChunk001.relation202_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1538 128 := by cbv
private def targetRows : List BasisRow := [⟨11, 88, 0, "13,1,67,1"⟩,
  ⟨11, 88, 1, "0,4,128,1"⟩,
  ⟨10, 88, 1, "9,1,75,1"⟩,
  ⟨9, 88, 0, "0,2,2,1,122,1"⟩,
  ⟨8, 88, 0, "0,3,9,1,69,1"⟩,
  ⟨7, 88, 0, "2,1,130,1"⟩,
  ⟨6, 88, 1, "2,1,131,1"⟩,
  ⟨5, 88, 1, "2,1,132,1"⟩,
  ⟨4, 88, 1, "2,2,7,1,69,1"⟩,
  ⟨89, 89, 0, "0,89"⟩,
  ⟨30, 89, 0, "0,1,140,1"⟩,
  ⟨27, 89, 0, "0,5,17,1,50,1"⟩,
  ⟨26, 89, 0, "0,2,8,1,77,1"⟩,
  ⟨26, 89, 1, "0,25,69,1"⟩,
  ⟨25, 89, 0, "0,2,8,1,78,1"⟩,
  ⟨20, 89, 0, "0,2,137,1"⟩,
  ⟨19, 89, 1, "0,2,138,1"⟩,
  ⟨16, 89, 0, "0,2,8,1,79,1"⟩,
  ⟨15, 89, 0, "0,2,8,1,80,1"⟩,
  ⟨12, 89, 1, "0,5,128,1"⟩,
  ⟨11, 89, 0, "0,1,141,1"⟩,
  ⟨10, 89, 0, "1,1,139,1"⟩,
  ⟨9, 89, 0, "2,1,134,1"⟩,
  ⟨9, 89, 1, "1,1,12,1,69,1"⟩,
  ⟨8, 89, 0, "7,1,95,1"⟩,
  ⟨7, 89, 0, "0,1,7,1,92,1"⟩,
  ⟨7, 89, 1, "0,1,2,1,131,1"⟩,
  ⟨6, 89, 0, "0,1,13,1,69,1"⟩,
  ⟨5, 89, 0, "0,1,142,1"⟩,
  ⟨4, 89, 0, "0,1,143,1"⟩,
  ⟨90, 90, 0, "0,90"⟩,
  ⟨31, 90, 0, "0,2,140,1"⟩,
  ⟨27, 90, 0, "0,26,69,1"⟩,
  ⟨23, 90, 0, "8,2,50,1"⟩,
  ⟨22, 90, 0, "16,1,17,2"⟩,
  ⟨21, 90, 0, "8,1,88,1"⟩,
  ⟨21, 90, 1, "0,3,137,1"⟩,
  ⟨20, 90, 0, "8,5"⟩,
  ⟨20, 90, 1, "0,3,138,1"⟩,
  ⟨19, 90, 0, "8,3,22,1"⟩,
  ⟨18, 90, 1, "8,3,23,1"⟩,
  ⟨17, 90, 0, "147,1"⟩,
  ⟨17, 90, 1, "8,2,51,1"⟩,
  ⟨16, 90, 0, "8,1,13,3"⟩,
  ⟨15, 90, 0, "13,2,32,1"⟩,
  ⟨14, 90, 0, "13,2,33,1"⟩,
  ⟨13, 90, 0, "9,1,80,1"⟩,
  ⟨13, 90, 1, "0,6,128,1"⟩,
  ⟨12, 90, 0, "0,2,141,1"⟩,
  ⟨11, 90, 0, "1,1,141,1"⟩,
  ⟨9, 90, 0, "3,1,120,1"⟩,
  ⟨8, 90, 0, "3,1,121,1"⟩,
  ⟨8, 90, 1, "0,2,7,1,92,1"⟩,
  ⟨7, 90, 1, "0,2,13,1,69,1"⟩,
  ⟨6, 90, 0, "1,1,13,1,69,1"⟩,
  ⟨6, 90, 1, "0,2,142,1"⟩,
  ⟨5, 90, 0, "2,1,11,1,69,1"⟩,
  ⟨5, 90, 2, "0,2,143,1"⟩,
  ⟨91, 91, 0, "0,91"⟩,
  ⟨29, 91, 0, "0,1,145,1"⟩,
  ⟨28, 91, 0, "0,27,69,1"⟩,
  ⟨25, 91, 0, "0,1,8,2,49,1"⟩,
  ⟨24, 91, 0, "0,1,8,2,50,1"⟩,
  ⟨22, 91, 0, "0,4,137,1"⟩,
  ⟨21, 91, 0, "0,4,138,1"⟩,
  ⟨19, 91, 0, "0,1,146,1"⟩,
  ⟨18, 91, 0, "0,1,147,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row921_mem, Shared.BasisChunk000.row922_mem, Shared.BasisChunk000.row924_mem, Shared.BasisChunk000.row925_mem, Shared.BasisChunk000.row926_mem, Shared.BasisChunk000.row927_mem, Shared.BasisChunk000.row929_mem, Shared.BasisChunk000.row931_mem, Shared.BasisChunk000.row933_mem, Shared.BasisChunk000.row935_mem, Shared.BasisChunk000.row936_mem, Shared.BasisChunk000.row937_mem, Shared.BasisChunk000.row938_mem, Shared.BasisChunk000.row939_mem, Shared.BasisChunk000.row940_mem, Shared.BasisChunk000.row941_mem, Shared.BasisChunk000.row943_mem, Shared.BasisChunk000.row944_mem, Shared.BasisChunk000.row945_mem, Shared.BasisChunk000.row947_mem, Shared.BasisChunk000.row948_mem, Shared.BasisChunk000.row949_mem, Shared.BasisChunk000.row950_mem, Shared.BasisChunk000.row951_mem, Shared.BasisChunk000.row952_mem, Shared.BasisChunk000.row953_mem, Shared.BasisChunk000.row954_mem, Shared.BasisChunk000.row955_mem, Shared.BasisChunk000.row956_mem, Shared.BasisChunk000.row957_mem, Shared.BasisChunk000.row958_mem, Shared.BasisChunk000.row959_mem, Shared.BasisChunk000.row961_mem, Shared.BasisChunk000.row963_mem, Shared.BasisChunk000.row964_mem, Shared.BasisChunk000.row965_mem, Shared.BasisChunk000.row966_mem, Shared.BasisChunk000.row967_mem, Shared.BasisChunk000.row968_mem, Shared.BasisChunk000.row969_mem, Shared.BasisChunk000.row971_mem, Shared.BasisChunk000.row972_mem, Shared.BasisChunk000.row973_mem, Shared.BasisChunk000.row974_mem, Shared.BasisChunk000.row975_mem, Shared.BasisChunk000.row976_mem, Shared.BasisChunk000.row978_mem, Shared.BasisChunk000.row979_mem, Shared.BasisChunk000.row980_mem, Shared.BasisChunk000.row981_mem, Shared.BasisChunk000.row983_mem, Shared.BasisChunk000.row984_mem, Shared.BasisChunk000.row985_mem, Shared.BasisChunk000.row987_mem, Shared.BasisChunk000.row988_mem, Shared.BasisChunk000.row989_mem, Shared.BasisChunk000.row990_mem, Shared.BasisChunk000.row992_mem, Shared.BasisChunk000.row994_mem, Shared.BasisChunk000.row995_mem, Shared.BasisChunk000.row996_mem, Shared.BasisChunk000.row997_mem, Shared.BasisChunk000.row998_mem, Shared.BasisChunk000.row999_mem, Shared.BasisChunk000.row1000_mem, Shared.BasisChunk000.row1002_mem, Shared.BasisChunk000.row1003_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard012
