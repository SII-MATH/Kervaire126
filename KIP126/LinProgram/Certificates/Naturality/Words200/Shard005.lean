import KIP126.LinProgram.Generated.Naturality.Words200.Shard005
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard005
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard005
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
  exact ⟨Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 642 128 := by cbv
private def targetRows : List BasisRow := [⟨64, 64, 0, "0,64"⟩,
  ⟨21, 64, 0, "65,1"⟩,
  ⟨18, 64, 0, "0,4,17,2"⟩,
  ⟨17, 64, 0, "0,1,8,1,39,1"⟩,
  ⟨17, 64, 1, "0,4,59,1"⟩,
  ⟨16, 64, 0, "0,1,8,1,40,1"⟩,
  ⟨15, 64, 0, "0,1,17,1,20,1"⟩,
  ⟨11, 64, 0, "0,1,64,1"⟩,
  ⟨10, 64, 0, "66,1"⟩,
  ⟨10, 64, 1, "0,2,17,1,18,1"⟩,
  ⟨6, 64, 0, "68,1"⟩,
  ⟨65, 65, 0, "0,65"⟩,
  ⟨22, 65, 0, "0,1,65,1"⟩,
  ⟨19, 65, 0, "0,5,17,2"⟩,
  ⟨18, 65, 0, "0,2,8,1,39,1"⟩,
  ⟨18, 65, 1, "0,5,59,1"⟩,
  ⟨17, 65, 0, "0,2,8,1,40,1"⟩,
  ⟨12, 65, 0, "0,2,64,1"⟩,
  ⟨11, 65, 1, "0,1,66,1"⟩,
  ⟨8, 65, 0, "18,1,20,1"⟩,
  ⟨8, 65, 1, "0,1,67,1"⟩,
  ⟨7, 65, 0, "0,1,68,1"⟩,
  ⟨3, 65, 0, "0,1,18,2"⟩,
  ⟨2, 65, 0, "0,1,69,1"⟩,
  ⟨66, 66, 0, "0,66"⟩,
  ⟨23, 66, 0, "0,2,65,1"⟩,
  ⟨19, 66, 0, "0,6,59,1"⟩,
  ⟨15, 66, 0, "8,2,17,1"⟩,
  ⟨14, 66, 0, "16,1,23,1"⟩,
  ⟨13, 66, 0, "8,1,42,1"⟩,
  ⟨13, 66, 1, "0,3,64,1"⟩,
  ⟨12, 66, 0, "8,1,13,2"⟩,
  ⟨12, 66, 1, "0,2,66,1"⟩,
  ⟨11, 66, 0, "13,1,32,1"⟩,
  ⟨10, 66, 1, "13,1,33,1"⟩,
  ⟨9, 66, 0, "0,1,18,1,20,1"⟩,
  ⟨9, 66, 1, "0,2,67,1"⟩,
  ⟨8, 66, 0, "0,2,68,1"⟩,
  ⟨4, 66, 0, "0,2,18,2"⟩,
  ⟨3, 66, 1, "0,2,69,1"⟩,
  ⟨67, 67, 0, "0,67"⟩,
  ⟨21, 67, 0, "0,1,71,1"⟩,
  ⟨20, 67, 0, "0,7,59,1"⟩,
  ⟨17, 67, 0, "0,1,8,2,16,1"⟩,
  ⟨16, 67, 0, "0,1,8,2,17,1"⟩,
  ⟨14, 67, 0, "0,4,64,1"⟩,
  ⟨13, 67, 0, "0,3,66,1"⟩,
  ⟨11, 67, 0, "0,1,72,1"⟩,
  ⟨10, 67, 0, "0,2,18,1,20,1"⟩,
  ⟨6, 67, 0, "75,1"⟩,
  ⟨6, 67, 1, "74,1"⟩,
  ⟨5, 67, 1, "1,1,70,1"⟩,
  ⟨5, 67, 2, "0,3,18,2"⟩,
  ⟨4, 67, 0, "0,3,69,1"⟩,
  ⟨68, 68, 0, "0,68"⟩,
  ⟨22, 68, 0, "0,2,71,1"⟩,
  ⟨21, 68, 1, "0,8,59,1"⟩,
  ⟨18, 68, 0, "0,2,8,2,16,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row387_mem, Shared.BasisChunk000.row389_mem, Shared.BasisChunk000.row390_mem, Shared.BasisChunk000.row391_mem, Shared.BasisChunk000.row392_mem, Shared.BasisChunk000.row393_mem, Shared.BasisChunk000.row394_mem, Shared.BasisChunk000.row395_mem, Shared.BasisChunk000.row396_mem, Shared.BasisChunk000.row397_mem, Shared.BasisChunk000.row399_mem, Shared.BasisChunk000.row402_mem, Shared.BasisChunk000.row403_mem, Shared.BasisChunk000.row404_mem, Shared.BasisChunk000.row405_mem, Shared.BasisChunk000.row406_mem, Shared.BasisChunk000.row407_mem, Shared.BasisChunk000.row408_mem, Shared.BasisChunk000.row410_mem, Shared.BasisChunk000.row412_mem, Shared.BasisChunk000.row413_mem, Shared.BasisChunk000.row414_mem, Shared.BasisChunk000.row416_mem, Shared.BasisChunk000.row417_mem, Shared.BasisChunk000.row418_mem, Shared.BasisChunk000.row419_mem, Shared.BasisChunk000.row421_mem, Shared.BasisChunk000.row423_mem, Shared.BasisChunk000.row424_mem, Shared.BasisChunk000.row425_mem, Shared.BasisChunk000.row426_mem, Shared.BasisChunk000.row427_mem, Shared.BasisChunk000.row428_mem, Shared.BasisChunk000.row429_mem, Shared.BasisChunk000.row431_mem, Shared.BasisChunk000.row432_mem, Shared.BasisChunk000.row433_mem, Shared.BasisChunk000.row434_mem, Shared.BasisChunk000.row435_mem, Shared.BasisChunk000.row437_mem, Shared.BasisChunk000.row439_mem, Shared.BasisChunk000.row440_mem, Shared.BasisChunk000.row441_mem, Shared.BasisChunk000.row442_mem, Shared.BasisChunk000.row443_mem, Shared.BasisChunk000.row444_mem, Shared.BasisChunk000.row445_mem, Shared.BasisChunk000.row447_mem, Shared.BasisChunk000.row448_mem, Shared.BasisChunk000.row450_mem, Shared.BasisChunk000.row451_mem, Shared.BasisChunk000.row453_mem, Shared.BasisChunk000.row454_mem, Shared.BasisChunk000.row455_mem, Shared.BasisChunk000.row456_mem, Shared.BasisChunk000.row457_mem, Shared.BasisChunk000.row459_mem, Shared.BasisChunk000.row460_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard005
