import KIP126.LinProgram.Generated.Naturality.Words200.Shard006
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard006
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard006
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
  exact ⟨Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation103_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation108_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 770 128 := by cbv
private def targetRows : List BasisRow := [⟨17, 68, 0, "0,2,8,2,17,1"⟩,
  ⟨15, 68, 0, "0,5,64,1"⟩,
  ⟨14, 68, 0, "0,4,66,1"⟩,
  ⟨12, 68, 0, "0,2,72,1"⟩,
  ⟨11, 68, 0, "1,1,72,1"⟩,
  ⟨8, 68, 0, "0,1,73,1"⟩,
  ⟨7, 68, 0, "0,1,75,1"⟩,
  ⟨7, 68, 1, "0,1,74,1"⟩,
  ⟨6, 68, 0, "18,1,24,1"⟩,
  ⟨6, 68, 1, "0,4,18,2"⟩,
  ⟨5, 68, 0, "0,4,69,1"⟩,
  ⟨3, 68, 0, "2,1,18,2"⟩,
  ⟨2, 68, 0, "2,1,69,1"⟩,
  ⟨69, 69, 0, "0,69"⟩,
  ⟨22, 69, 0, "0,9,59,1"⟩,
  ⟨19, 69, 0, "78,1"⟩,
  ⟨16, 69, 1, "0,6,64,1"⟩,
  ⟨15, 69, 0, "8,2,20,1"⟩,
  ⟨15, 69, 1, "0,5,66,1"⟩,
  ⟨14, 69, 0, "8,1,45,1"⟩,
  ⟨13, 69, 0, "8,1,46,1"⟩,
  ⟨13, 69, 1, "0,3,72,1"⟩,
  ⟨12, 69, 0, "9,1,13,2"⟩,
  ⟨9, 69, 0, "80,1"⟩,
  ⟨9, 69, 1, "0,2,73,1"⟩,
  ⟨8, 69, 0, "0,2,74,1"⟩,
  ⟨7, 69, 0, "0,5,18,2"⟩,
  ⟨6, 69, 0, "1,1,76,1"⟩,
  ⟨6, 69, 1, "0,5,69,1"⟩,
  ⟨5, 69, 0, "2,1,70,1"⟩,
  ⟨4, 69, 0, "0,1,2,1,18,2"⟩,
  ⟨3, 69, 0, "0,1,2,1,69,1"⟩,
  ⟨70, 70, 0, "0,70"⟩,
  ⟨23, 70, 0, "0,10,59,1"⟩,
  ⟨21, 70, 0, "0,1,77,1"⟩,
  ⟨20, 70, 0, "0,1,78,1"⟩,
  ⟨17, 70, 0, "0,7,64,1"⟩,
  ⟨16, 70, 0, "0,6,66,1"⟩,
  ⟨11, 70, 0, "0,1,79,1"⟩,
  ⟨10, 70, 0, "0,1,80,1"⟩,
  ⟨8, 70, 0, "83,1"⟩,
  ⟨8, 70, 2, "0,6,18,2"⟩,
  ⟨7, 70, 2, "0,6,69,1"⟩,
  ⟨6, 70, 0, "86,1"⟩,
  ⟨5, 70, 0, "0,2,2,1,18,2"⟩,
  ⟨4, 70, 0, "0,2,2,1,69,1"⟩,
  ⟨71, 71, 0, "0,71"⟩,
  ⟨24, 71, 0, "0,11,59,1"⟩,
  ⟨22, 71, 0, "0,2,77,1"⟩,
  ⟨21, 71, 0, "0,2,78,1"⟩,
  ⟨18, 71, 0, "0,8,64,1"⟩,
  ⟨17, 71, 0, "0,7,66,1"⟩,
  ⟨12, 71, 0, "0,2,79,1"⟩,
  ⟨11, 71, 0, "1,1,79,1"⟩,
  ⟨11, 71, 1, "0,2,80,1"⟩,
  ⟨10, 71, 0, "0,1,81,1"⟩,
  ⟨9, 71, 0, "0,7,18,2"⟩,
  ⟨8, 71, 0, "0,1,84,1"⟩,
  ⟨8, 71, 1, "0,7,69,1"⟩,
  ⟨7, 71, 0, "2,1,75,1"⟩,
  ⟨7, 71, 1, "0,1,86,1"⟩,
  ⟨6, 71, 0, "2,1,76,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row461_mem, Shared.BasisChunk000.row462_mem, Shared.BasisChunk000.row463_mem, Shared.BasisChunk000.row464_mem, Shared.BasisChunk000.row465_mem, Shared.BasisChunk000.row466_mem, Shared.BasisChunk000.row467_mem, Shared.BasisChunk000.row468_mem, Shared.BasisChunk000.row469_mem, Shared.BasisChunk000.row470_mem, Shared.BasisChunk000.row471_mem, Shared.BasisChunk000.row473_mem, Shared.BasisChunk000.row475_mem, Shared.BasisChunk000.row476_mem, Shared.BasisChunk000.row477_mem, Shared.BasisChunk000.row479_mem, Shared.BasisChunk000.row481_mem, Shared.BasisChunk000.row482_mem, Shared.BasisChunk000.row483_mem, Shared.BasisChunk000.row484_mem, Shared.BasisChunk000.row485_mem, Shared.BasisChunk000.row486_mem, Shared.BasisChunk000.row487_mem, Shared.BasisChunk000.row489_mem, Shared.BasisChunk000.row490_mem, Shared.BasisChunk000.row491_mem, Shared.BasisChunk000.row492_mem, Shared.BasisChunk000.row493_mem, Shared.BasisChunk000.row494_mem, Shared.BasisChunk000.row495_mem, Shared.BasisChunk000.row496_mem, Shared.BasisChunk000.row497_mem, Shared.BasisChunk000.row498_mem, Shared.BasisChunk000.row499_mem, Shared.BasisChunk000.row501_mem, Shared.BasisChunk000.row502_mem, Shared.BasisChunk000.row503_mem, Shared.BasisChunk000.row504_mem, Shared.BasisChunk000.row505_mem, Shared.BasisChunk000.row506_mem, Shared.BasisChunk000.row508_mem, Shared.BasisChunk000.row510_mem, Shared.BasisChunk000.row513_mem, Shared.BasisChunk000.row514_mem, Shared.BasisChunk000.row515_mem, Shared.BasisChunk000.row516_mem, Shared.BasisChunk000.row517_mem, Shared.BasisChunk000.row518_mem, Shared.BasisChunk000.row520_mem, Shared.BasisChunk000.row521_mem, Shared.BasisChunk000.row522_mem, Shared.BasisChunk000.row523_mem, Shared.BasisChunk000.row524_mem, Shared.BasisChunk000.row525_mem, Shared.BasisChunk000.row526_mem, Shared.BasisChunk000.row527_mem, Shared.BasisChunk000.row528_mem, Shared.BasisChunk000.row529_mem, Shared.BasisChunk000.row530_mem, Shared.BasisChunk000.row531_mem, Shared.BasisChunk000.row532_mem, Shared.BasisChunk000.row533_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard006
