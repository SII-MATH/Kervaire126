import KIP126.LinProgram.Generated.Naturality.Words200.Shard002
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard002
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard002
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
  exact ⟨Shared.RelationChunk000.relation3_zero, Shared.RelationChunk000.relation38_zero, Shared.RelationChunk000.relation45_zero, Shared.RelationChunk000.relation46_zero, Shared.RelationChunk000.relation51_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 258 128 := by cbv
private def targetRows : List BasisRow := [⟨4, 38, 0, "0,2,2,1,18,1"⟩,
  ⟨39, 39, 0, "0,39"⟩,
  ⟨9, 39, 0, "0,3,23,1"⟩,
  ⟨8, 39, 1, "0,7,18,1"⟩,
  ⟨7, 39, 0, "29,1"⟩,
  ⟨40, 40, 0, "0,40"⟩,
  ⟨13, 40, 0, "30,1"⟩,
  ⟨10, 40, 0, "0,4,23,1"⟩,
  ⟨9, 40, 0, "0,1,8,1,9,1"⟩,
  ⟨9, 40, 1, "0,8,18,1"⟩,
  ⟨8, 40, 0, "0,1,29,1"⟩,
  ⟨7, 40, 0, "1,1,28,1"⟩,
  ⟨6, 40, 0, "2,1,24,1"⟩,
  ⟨5, 40, 0, "2,1,25,1"⟩,
  ⟨3, 40, 0, "2,2,18,1"⟩,
  ⟨41, 41, 0, "0,41"⟩,
  ⟨14, 41, 0, "0,1,30,1"⟩,
  ⟨11, 41, 0, "0,5,23,1"⟩,
  ⟨10, 41, 0, "0,2,8,1,9,1"⟩,
  ⟨10, 41, 1, "0,9,18,1"⟩,
  ⟨9, 41, 0, "0,2,29,1"⟩,
  ⟨3, 41, 0, "0,1,3,1,18,1"⟩,
  ⟨42, 42, 0, "0,42"⟩,
  ⟨15, 42, 0, "0,2,30,1"⟩,
  ⟨11, 42, 0, "0,10,18,1"⟩,
  ⟨7, 42, 0, "32,1"⟩,
  ⟨4, 42, 1, "0,2,3,1,18,1"⟩,
  ⟨43, 43, 0, "0,43"⟩,
  ⟨13, 43, 0, "0,1,31,1"⟩,
  ⟨12, 43, 0, "0,11,18,1"⟩,
  ⟨9, 43, 0, "0,1,8,1,13,1"⟩,
  ⟨8, 43, 0, "0,1,32,1"⟩,
  ⟨6, 43, 0, "0,1,34,1"⟩,
  ⟨5, 43, 0, "0,3,3,1,18,1"⟩,
  ⟨44, 44, 0, "0,44"⟩,
  ⟨14, 44, 0, "0,2,31,1"⟩,
  ⟨13, 44, 1, "0,12,18,1"⟩,
  ⟨10, 44, 0, "0,2,8,1,13,1"⟩,
  ⟨9, 44, 0, "0,2,32,1"⟩,
  ⟨7, 44, 0, "1,1,33,1"⟩,
  ⟨7, 44, 1, "0,2,34,1"⟩,
  ⟨6, 44, 1, "1,1,34,1"⟩,
  ⟨4, 44, 1, "1,2,3,1,18,1"⟩,
  ⟨3, 44, 0, "38,1"⟩,
  ⟨45, 45, 0, "0,45"⟩,
  ⟨14, 45, 0, "0,13,18,1"⟩,
  ⟨11, 45, 0, "40,1"⟩,
  ⟨8, 45, 1, "0,3,34,1"⟩,
  ⟨7, 45, 0, "0,1,36,1"⟩,
  ⟨5, 45, 0, "1,1,4,1,18,1"⟩,
  ⟨5, 45, 1, "0,1,37,1"⟩,
  ⟨4, 45, 0, "0,1,38,1"⟩,
  ⟨46, 46, 0, "0,46"⟩,
  ⟨15, 46, 0, "0,14,18,1"⟩,
  ⟨13, 46, 0, "0,1,39,1"⟩,
  ⟨12, 46, 0, "0,1,40,1"⟩,
  ⟨9, 46, 0, "0,4,34,1"⟩,
  ⟨8, 46, 0, "0,2,36,1"⟩,
  ⟨7, 46, 0, "1,1,36,1"⟩,
  ⟨6, 46, 1, "0,2,37,1"⟩,
  ⟨5, 46, 0, "0,2,38,1"⟩,
  ⟨47, 47, 0, "0,47"⟩,
  ⟨16, 47, 0, "0,15,18,1"⟩,
  ⟨14, 47, 0, "0,2,39,1"⟩,
  ⟨13, 47, 0, "0,2,40,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row154_mem, Shared.BasisChunk000.row155_mem, Shared.BasisChunk000.row156_mem, Shared.BasisChunk000.row158_mem, Shared.BasisChunk000.row159_mem, Shared.BasisChunk000.row160_mem, Shared.BasisChunk000.row162_mem, Shared.BasisChunk000.row163_mem, Shared.BasisChunk000.row164_mem, Shared.BasisChunk000.row165_mem, Shared.BasisChunk000.row166_mem, Shared.BasisChunk000.row167_mem, Shared.BasisChunk000.row168_mem, Shared.BasisChunk000.row169_mem, Shared.BasisChunk000.row170_mem, Shared.BasisChunk000.row172_mem, Shared.BasisChunk000.row173_mem, Shared.BasisChunk000.row174_mem, Shared.BasisChunk000.row175_mem, Shared.BasisChunk000.row176_mem, Shared.BasisChunk000.row177_mem, Shared.BasisChunk000.row178_mem, Shared.BasisChunk000.row179_mem, Shared.BasisChunk000.row180_mem, Shared.BasisChunk000.row182_mem, Shared.BasisChunk000.row184_mem, Shared.BasisChunk000.row188_mem, Shared.BasisChunk000.row190_mem, Shared.BasisChunk000.row191_mem, Shared.BasisChunk000.row192_mem, Shared.BasisChunk000.row193_mem, Shared.BasisChunk000.row194_mem, Shared.BasisChunk000.row195_mem, Shared.BasisChunk000.row196_mem, Shared.BasisChunk000.row198_mem, Shared.BasisChunk000.row199_mem, Shared.BasisChunk000.row201_mem, Shared.BasisChunk000.row202_mem, Shared.BasisChunk000.row203_mem, Shared.BasisChunk000.row204_mem, Shared.BasisChunk000.row205_mem, Shared.BasisChunk000.row207_mem, Shared.BasisChunk000.row210_mem, Shared.BasisChunk000.row211_mem, Shared.BasisChunk000.row212_mem, Shared.BasisChunk000.row213_mem, Shared.BasisChunk000.row215_mem, Shared.BasisChunk000.row217_mem, Shared.BasisChunk000.row218_mem, Shared.BasisChunk000.row219_mem, Shared.BasisChunk000.row220_mem, Shared.BasisChunk000.row221_mem, Shared.BasisChunk000.row222_mem, Shared.BasisChunk000.row223_mem, Shared.BasisChunk000.row225_mem, Shared.BasisChunk000.row226_mem, Shared.BasisChunk000.row227_mem, Shared.BasisChunk000.row228_mem, Shared.BasisChunk000.row229_mem, Shared.BasisChunk000.row231_mem, Shared.BasisChunk000.row232_mem, Shared.BasisChunk000.row233_mem, Shared.BasisChunk000.row234_mem, Shared.BasisChunk000.row236_mem, Shared.BasisChunk000.row237_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard002
