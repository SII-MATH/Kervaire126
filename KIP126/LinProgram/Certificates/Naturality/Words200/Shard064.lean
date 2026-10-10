import KIP126.LinProgram.Generated.Naturality.Words200.Shard064
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk020
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard064
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard064
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
  exact ⟨Shared.RelationChunk000.relation20_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk010.relation551_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk011.relation604_zero, Shared.RelationChunk011.relation605_zero, Shared.RelationChunk011.relation609_zero, Shared.RelationChunk011.relation610_zero, Shared.RelationChunk011.relation612_zero, Shared.RelationChunk011.relation613_zero, Shared.RelationChunk011.relation614_zero, Shared.RelationChunk011.relation615_zero, Shared.RelationChunk011.relation616_zero, Shared.RelationChunk011.relation617_zero, Shared.RelationChunk020.relation916_zero, Shared.RelationChunk020.relation918_zero, Shared.RelationChunk020.relation919_zero, Shared.RelationChunk020.relation920_zero, Shared.RelationChunk020.relation921_zero, Shared.RelationChunk020.relation922_zero, Shared.RelationChunk020.relation923_zero, Shared.RelationChunk020.relation924_zero, Shared.RelationChunk020.relation925_zero, Shared.RelationChunk020.relation926_zero, Shared.RelationChunk020.relation927_zero, Shared.RelationChunk020.relation928_zero, Shared.RelationChunk020.relation929_zero, Shared.RelationChunk020.relation930_zero, Shared.RelationChunk020.relation931_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8194 128 := by cbv
private def targetRows : List BasisRow := [⟨161, 161, 0, "0,161"⟩,
  ⟨54, 161, 0, "0,1,641,1"⟩,
  ⟨51, 161, 0, "0,5,17,1,296,1"⟩,
  ⟨50, 161, 0, "0,2,8,1,469,1"⟩,
  ⟨50, 161, 1, "0,5,606,1"⟩,
  ⟨49, 161, 0, "0,2,8,1,470,1"⟩,
  ⟨44, 161, 0, "0,2,635,1"⟩,
  ⟨43, 161, 1, "0,2,636,1"⟩,
  ⟨40, 161, 0, "0,2,8,1,16,1,224,1"⟩,
  ⟨39, 161, 0, "0,2,8,1,16,1,225,1"⟩,
  ⟨35, 161, 0, "17,1,343,1"⟩,
  ⟨35, 161, 1, "0,17,500,1"⟩,
  ⟨34, 161, 0, "8,1,489,1"⟩,
  ⟨34, 161, 1, "0,33,324,1"⟩,
  ⟨33, 161, 0, "8,1,490,1"⟩,
  ⟨33, 161, 1, "0,3,623,1"⟩,
  ⟨32, 161, 0, "8,3,206,1"⟩,
  ⟨32, 161, 1, "0,6,64,1,149,1"⟩,
  ⟨31, 161, 0, "8,2,17,1,160,1"⟩,
  ⟨31, 161, 1, "0,6,598,1"⟩,
  ⟨30, 161, 1, "8,3,207,1"⟩,
  ⟨29, 161, 0, "8,3,208,1"⟩,
  ⟨29, 161, 1, "0,6,601,1"⟩,
  ⟨29, 161, 2, "0,6,600,1"⟩,
  ⟨28, 161, 0, "8,2,9,1,194,1"⟩,
  ⟨27, 161, 1, "8,1,9,1,13,1,167,1"⟩,
  ⟨26, 161, 0, "16,1,347,1"⟩,
  ⟨26, 161, 1, "9,1,13,1,248,1"⟩,
  ⟨25, 161, 0, "17,1,347,1"⟩,
  ⟨25, 161, 1, "8,2,292,1"⟩,
  ⟨25, 161, 2, "0,1,642,1"⟩,
  ⟨24, 161, 0, "654,1"⟩,
  ⟨24, 161, 1, "22,1,292,1"⟩,
  ⟨24, 161, 2, "8,1,492,1"⟩,
  ⟨23, 161, 0, "23,1,292,1"⟩,
  ⟨23, 161, 1, "8,2,293,1"⟩,
  ⟨23, 161, 2, "0,1,643,1"⟩,
  ⟨23, 161, 3, "0,3,627,1"⟩,
  ⟨22, 161, 0, "8,3,209,1"⟩,
  ⟨22, 161, 1, "0,1,645,1"⟩,
  ⟨22, 161, 2, "0,1,644,1"⟩,
  ⟨21, 161, 0, "8,2,294,1"⟩,
  ⟨21, 161, 1, "0,1,646,1"⟩,
  ⟨21, 161, 2, "0,9,575,1"⟩,
  ⟨20, 161, 1, "8,1,13,1,261,1"⟩,
  ⟨20, 161, 3, "0,1,8,1,69,1,112,1"⟩,
  ⟨20, 161, 4, "0,4,17,1,314,1"⟩,
  ⟨19, 161, 0, "13,1,423,1"⟩,
  ⟨19, 161, 1, "1,1,639,1"⟩,
  ⟨19, 161, 2, "0,1,8,1,69,1,113,1"⟩,
  ⟨19, 161, 3, "0,2,8,1,475,1"⟩,
  ⟨18, 161, 0, "656,1"⟩,
  ⟨18, 161, 1, "13,1,23,1,181,1"⟩,
  ⟨18, 161, 2, "0,1,8,1,483,1"⟩,
  ⟨18, 161, 3, "0,2,17,1,333,1"⟩,
  ⟨17, 161, 0, "2,1,618,1"⟩,
  ⟨17, 161, 1, "0,1,648,1"⟩,
  ⟨16, 161, 0, "0,1,650,1"⟩,
  ⟨14, 161, 0, "0,3,631,1"⟩,
  ⟨13, 161, 1, "0,1,652,1"⟩,
  ⟨13, 161, 2, "0,2,7,2,314,1"⟩,
  ⟨12, 161, 0, "13,1,69,1,95,1"⟩,
  ⟨12, 161, 1, "0,2,18,1,314,1"⟩,
  ⟨12, 161, 2, "0,3,17,1,69,2"⟩,
  ⟨11, 161, 0, "18,1,332,1"⟩,
  ⟨11, 161, 1, "0,1,68,1,163,1"⟩,
  ⟨11, 161, 2, "0,3,17,1,324,1"⟩,
  ⟨10, 161, 0, "658,1"⟩,
  ⟨9, 161, 0, "659,1"⟩,
  ⟨9, 161, 1, "20,1,69,2"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4918_mem, Shared.BasisChunk004.row4919_mem, Shared.BasisChunk004.row4920_mem, Shared.BasisChunk004.row4921_mem, Shared.BasisChunk004.row4922_mem, Shared.BasisChunk004.row4923_mem, Shared.BasisChunk004.row4924_mem, Shared.BasisChunk004.row4926_mem, Shared.BasisChunk004.row4927_mem, Shared.BasisChunk004.row4928_mem, Shared.BasisChunk004.row4931_mem, Shared.BasisChunk004.row4932_mem, Shared.BasisChunk004.row4933_mem, Shared.BasisChunk004.row4934_mem, Shared.BasisChunk004.row4935_mem, Shared.BasisChunk004.row4936_mem, Shared.BasisChunk004.row4937_mem, Shared.BasisChunk004.row4938_mem, Shared.BasisChunk004.row4939_mem, Shared.BasisChunk004.row4940_mem, Shared.BasisChunk004.row4942_mem, Shared.BasisChunk004.row4943_mem, Shared.BasisChunk004.row4944_mem, Shared.BasisChunk004.row4945_mem, Shared.BasisChunk004.row4946_mem, Shared.BasisChunk004.row4948_mem, Shared.BasisChunk004.row4949_mem, Shared.BasisChunk004.row4950_mem, Shared.BasisChunk004.row4952_mem, Shared.BasisChunk004.row4953_mem, Shared.BasisChunk004.row4954_mem, Shared.BasisChunk004.row4955_mem, Shared.BasisChunk004.row4956_mem, Shared.BasisChunk004.row4957_mem, Shared.BasisChunk004.row4958_mem, Shared.BasisChunk004.row4959_mem, Shared.BasisChunk004.row4960_mem, Shared.BasisChunk004.row4961_mem, Shared.BasisChunk004.row4962_mem, Shared.BasisChunk004.row4963_mem, Shared.BasisChunk004.row4964_mem, Shared.BasisChunk004.row4965_mem, Shared.BasisChunk004.row4966_mem, Shared.BasisChunk004.row4967_mem, Shared.BasisChunk004.row4969_mem, Shared.BasisChunk004.row4971_mem, Shared.BasisChunk004.row4972_mem, Shared.BasisChunk004.row4973_mem, Shared.BasisChunk004.row4974_mem, Shared.BasisChunk004.row4975_mem, Shared.BasisChunk004.row4976_mem, Shared.BasisChunk004.row4977_mem, Shared.BasisChunk004.row4978_mem, Shared.BasisChunk004.row4979_mem, Shared.BasisChunk004.row4980_mem, Shared.BasisChunk004.row4981_mem, Shared.BasisChunk004.row4982_mem, Shared.BasisChunk004.row4983_mem, Shared.BasisChunk004.row4984_mem, Shared.BasisChunk004.row4986_mem, Shared.BasisChunk004.row4987_mem, Shared.BasisChunk004.row4988_mem, Shared.BasisChunk004.row4989_mem, Shared.BasisChunk004.row4990_mem, Shared.BasisChunk004.row4991_mem, Shared.BasisChunk004.row4992_mem, Shared.BasisChunk004.row4993_mem, Shared.BasisChunk004.row4994_mem, Shared.BasisChunk004.row4997_mem, Shared.BasisChunk004.row4998_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard064
