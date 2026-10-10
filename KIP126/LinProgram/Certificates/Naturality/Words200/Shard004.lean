import KIP126.LinProgram.Generated.Naturality.Words200.Shard004
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard004
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard004
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
  exact ⟨Shared.RelationChunk000.relation16_zero, Shared.RelationChunk000.relation75_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 514 128 := by cbv
private def targetRows : List BasisRow := [⟨14, 56, 0, "0,2,8,3"⟩,
  ⟨13, 56, 0, "0,2,8,1,22,1"⟩,
  ⟨8, 56, 0, "0,1,53,1"⟩,
  ⟨6, 56, 0, "54,1"⟩,
  ⟨57, 57, 0, "0,57"⟩,
  ⟨18, 57, 0, "0,3,50,1"⟩,
  ⟨15, 57, 0, "56,1"⟩,
  ⟨12, 57, 0, "8,2,9,1"⟩,
  ⟨11, 57, 0, "8,1,29,1"⟩,
  ⟨10, 57, 0, "9,1,23,1"⟩,
  ⟨9, 57, 0, "1,1,12,1,18,1"⟩,
  ⟨9, 57, 1, "0,2,53,1"⟩,
  ⟨6, 57, 0, "0,1,3,1,43,1"⟩,
  ⟨5, 57, 0, "57,1"⟩,
  ⟨58, 58, 0, "0,58"⟩,
  ⟨19, 58, 0, "0,4,50,1"⟩,
  ⟨17, 58, 0, "0,1,55,1"⟩,
  ⟨16, 58, 0, "0,1,56,1"⟩,
  ⟨7, 58, 0, "0,2,3,1,43,1"⟩,
  ⟨6, 58, 0, "1,1,3,1,43,1"⟩,
  ⟨5, 58, 0, "2,1,11,1,18,1"⟩,
  ⟨59, 59, 0, "0,59"⟩,
  ⟨20, 59, 0, "0,5,50,1"⟩,
  ⟨18, 59, 0, "0,2,55,1"⟩,
  ⟨17, 59, 0, "0,2,56,1"⟩,
  ⟨8, 59, 0, "2,1,53,1"⟩,
  ⟨60, 60, 0, "0,60"⟩,
  ⟨19, 60, 0, "0,3,55,1"⟩,
  ⟨15, 60, 0, "16,1,17,1"⟩,
  ⟨14, 60, 0, "17,2"⟩,
  ⟨13, 60, 0, "60,1"⟩,
  ⟨12, 60, 0, "8,2,13,1"⟩,
  ⟨11, 60, 0, "8,1,32,1"⟩,
  ⟨10, 60, 0, "13,1,23,1"⟩,
  ⟨9, 60, 0, "13,1,24,1"⟩,
  ⟨8, 60, 0, "13,1,25,1"⟩,
  ⟨7, 60, 0, "2,1,54,1"⟩,
  ⟨61, 61, 0, "0,61"⟩,
  ⟨20, 61, 0, "1,1,58,1"⟩,
  ⟨17, 61, 0, "0,1,8,1,31,1"⟩,
  ⟨16, 61, 0, "0,1,16,1,17,1"⟩,
  ⟨15, 61, 0, "0,1,17,2"⟩,
  ⟨14, 61, 0, "0,1,59,1"⟩,
  ⟨62, 62, 0, "0,62"⟩,
  ⟨18, 62, 0, "0,2,8,1,31,1"⟩,
  ⟨17, 62, 0, "0,2,16,1,17,1"⟩,
  ⟨16, 62, 0, "0,2,17,2"⟩,
  ⟨15, 62, 0, "0,2,59,1"⟩,
  ⟨8, 62, 0, "17,1,18,1"⟩,
  ⟨7, 62, 0, "1,1,61,1"⟩,
  ⟨63, 63, 0, "0,63"⟩,
  ⟨17, 63, 0, "0,3,17,2"⟩,
  ⟨16, 63, 1, "0,3,59,1"⟩,
  ⟨15, 63, 0, "8,1,40,1"⟩,
  ⟨14, 63, 0, "17,1,20,1"⟩,
  ⟨13, 63, 0, "63,1"⟩,
  ⟨12, 63, 0, "8,1,9,1,13,1"⟩,
  ⟨11, 63, 0, "9,1,32,1"⟩,
  ⟨9, 63, 0, "0,1,17,1,18,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row316_mem, Shared.BasisChunk000.row317_mem, Shared.BasisChunk000.row318_mem, Shared.BasisChunk000.row319_mem, Shared.BasisChunk000.row321_mem, Shared.BasisChunk000.row322_mem, Shared.BasisChunk000.row324_mem, Shared.BasisChunk000.row325_mem, Shared.BasisChunk000.row326_mem, Shared.BasisChunk000.row327_mem, Shared.BasisChunk000.row328_mem, Shared.BasisChunk000.row329_mem, Shared.BasisChunk000.row330_mem, Shared.BasisChunk000.row331_mem, Shared.BasisChunk000.row332_mem, Shared.BasisChunk000.row333_mem, Shared.BasisChunk000.row335_mem, Shared.BasisChunk000.row336_mem, Shared.BasisChunk000.row337_mem, Shared.BasisChunk000.row338_mem, Shared.BasisChunk000.row339_mem, Shared.BasisChunk000.row340_mem, Shared.BasisChunk000.row341_mem, Shared.BasisChunk000.row343_mem, Shared.BasisChunk000.row344_mem, Shared.BasisChunk000.row345_mem, Shared.BasisChunk000.row346_mem, Shared.BasisChunk000.row347_mem, Shared.BasisChunk000.row349_mem, Shared.BasisChunk000.row350_mem, Shared.BasisChunk000.row351_mem, Shared.BasisChunk000.row353_mem, Shared.BasisChunk000.row354_mem, Shared.BasisChunk000.row355_mem, Shared.BasisChunk000.row356_mem, Shared.BasisChunk000.row357_mem, Shared.BasisChunk000.row358_mem, Shared.BasisChunk000.row360_mem, Shared.BasisChunk000.row361_mem, Shared.BasisChunk000.row362_mem, Shared.BasisChunk000.row363_mem, Shared.BasisChunk000.row364_mem, Shared.BasisChunk000.row365_mem, Shared.BasisChunk000.row366_mem, Shared.BasisChunk000.row368_mem, Shared.BasisChunk000.row369_mem, Shared.BasisChunk000.row370_mem, Shared.BasisChunk000.row371_mem, Shared.BasisChunk000.row374_mem, Shared.BasisChunk000.row375_mem, Shared.BasisChunk000.row376_mem, Shared.BasisChunk000.row377_mem, Shared.BasisChunk000.row379_mem, Shared.BasisChunk000.row380_mem, Shared.BasisChunk000.row381_mem, Shared.BasisChunk000.row382_mem, Shared.BasisChunk000.row383_mem, Shared.BasisChunk000.row384_mem, Shared.BasisChunk000.row386_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard004
