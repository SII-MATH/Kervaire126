import KIP126.LinProgram.Generated.Naturality.Words200.Shard031
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard031
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard031
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
  exact ⟨Shared.RelationChunk000.relation99_zero, Shared.RelationChunk003.relation287_zero, Shared.RelationChunk005.relation362_zero, Shared.RelationChunk007.relation432_zero, Shared.RelationChunk007.relation433_zero, Shared.RelationChunk007.relation434_zero, Shared.RelationChunk007.relation435_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3970 128 := by cbv
private def targetRows : List BasisRow := [⟨3, 129, 0, "0,1,69,2"⟩,
  ⟨2, 129, 0, "0,1,324,1"⟩,
  ⟨130, 130, 0, "0,130"⟩,
  ⟨43, 130, 0, "0,4,296,1"⟩,
  ⟨41, 130, 0, "0,1,325,1"⟩,
  ⟨40, 130, 0, "0,1,326,1"⟩,
  ⟨36, 130, 0, "0,14,245,1"⟩,
  ⟨35, 130, 0, "0,14,246,1"⟩,
  ⟨31, 130, 0, "0,1,8,1,224,1"⟩,
  ⟨30, 130, 0, "0,1,8,1,225,1"⟩,
  ⟨27, 130, 0, "0,1,8,2,16,1,64,1"⟩,
  ⟨26, 130, 1, "0,1,8,2,17,1,64,1"⟩,
  ⟨24, 130, 0, "0,4,64,2"⟩,
  ⟨23, 130, 0, "0,4,299,1"⟩,
  ⟨22, 130, 1, "0,5,292,1"⟩,
  ⟨21, 130, 0, "0,1,64,1,72,1"⟩,
  ⟨21, 130, 1, "0,4,301,1"⟩,
  ⟨21, 130, 2, "0,4,300,1"⟩,
  ⟨20, 130, 0, "0,1,327,1"⟩,
  ⟨20, 130, 1, "0,2,317,1"⟩,
  ⟨20, 130, 2, "0,2,316,1"⟩,
  ⟨19, 130, 0, "1,2,300,1"⟩,
  ⟨19, 130, 1, "0,1,2,1,292,1"⟩,
  ⟨18, 130, 1, "13,1,23,1,83,1"⟩,
  ⟨18, 130, 2, "0,2,3,1,266,1"⟩,
  ⟨17, 130, 0, "9,1,13,1,133,1"⟩,
  ⟨17, 130, 1, "2,1,302,1"⟩,
  ⟨17, 130, 2, "0,1,9,1,212,1"⟩,
  ⟨17, 130, 3, "0,2,3,1,267,1"⟩,
  ⟨16, 130, 0, "2,1,13,1,188,1"⟩,
  ⟨16, 130, 1, "0,1,328,1"⟩,
  ⟨15, 130, 0, "1,2,308,1"⟩,
  ⟨15, 130, 1, "0,2,319,1"⟩,
  ⟨13, 130, 0, "0,3,312,1"⟩,
  ⟨13, 130, 1, "0,3,311,1"⟩,
  ⟨12, 130, 2, "0,3,314,1"⟩,
  ⟨11, 130, 0, "336,1"⟩,
  ⟨11, 130, 3, "1,1,3,1,270,1"⟩,
  ⟨10, 130, 0, "337,1"⟩,
  ⟨10, 130, 1, "1,1,322,1"⟩,
  ⟨10, 130, 2, "0,1,333,1"⟩,
  ⟨9, 130, 0, "338,1"⟩,
  ⟨9, 130, 1, "0,2,68,1,69,1"⟩,
  ⟨8, 130, 0, "1,1,323,1"⟩,
  ⟨5, 130, 0, "340,1"⟩,
  ⟨4, 130, 0, "341,1"⟩,
  ⟨4, 130, 1, "0,2,69,2"⟩,
  ⟨3, 130, 1, "0,2,324,1"⟩,
  ⟨131, 131, 0, "0,131"⟩,
  ⟨44, 131, 0, "0,5,296,1"⟩,
  ⟨42, 131, 0, "0,2,325,1"⟩,
  ⟨41, 131, 0, "0,2,326,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2380_mem, Shared.BasisChunk002.row2381_mem, Shared.BasisChunk002.row2382_mem, Shared.BasisChunk002.row2383_mem, Shared.BasisChunk002.row2385_mem, Shared.BasisChunk002.row2386_mem, Shared.BasisChunk002.row2387_mem, Shared.BasisChunk002.row2388_mem, Shared.BasisChunk002.row2389_mem, Shared.BasisChunk002.row2390_mem, Shared.BasisChunk002.row2392_mem, Shared.BasisChunk002.row2394_mem, Shared.BasisChunk002.row2395_mem, Shared.BasisChunk002.row2396_mem, Shared.BasisChunk002.row2398_mem, Shared.BasisChunk002.row2399_mem, Shared.BasisChunk002.row2400_mem, Shared.BasisChunk002.row2401_mem, Shared.BasisChunk002.row2402_mem, Shared.BasisChunk002.row2403_mem, Shared.BasisChunk002.row2404_mem, Shared.BasisChunk002.row2405_mem, Shared.BasisChunk002.row2406_mem, Shared.BasisChunk002.row2408_mem, Shared.BasisChunk002.row2409_mem, Shared.BasisChunk002.row2410_mem, Shared.BasisChunk002.row2411_mem, Shared.BasisChunk002.row2412_mem, Shared.BasisChunk002.row2413_mem, Shared.BasisChunk002.row2414_mem, Shared.BasisChunk002.row2415_mem, Shared.BasisChunk002.row2416_mem, Shared.BasisChunk002.row2417_mem, Shared.BasisChunk002.row2419_mem, Shared.BasisChunk002.row2420_mem, Shared.BasisChunk002.row2423_mem, Shared.BasisChunk002.row2424_mem, Shared.BasisChunk002.row2427_mem, Shared.BasisChunk002.row2428_mem, Shared.BasisChunk002.row2429_mem, Shared.BasisChunk002.row2430_mem, Shared.BasisChunk002.row2431_mem, Shared.BasisChunk002.row2432_mem, Shared.BasisChunk002.row2433_mem, Shared.BasisChunk002.row2435_mem, Shared.BasisChunk002.row2436_mem, Shared.BasisChunk002.row2437_mem, Shared.BasisChunk002.row2439_mem, Shared.BasisChunk002.row2441_mem, Shared.BasisChunk002.row2442_mem, Shared.BasisChunk002.row2444_mem, Shared.BasisChunk002.row2445_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard031
