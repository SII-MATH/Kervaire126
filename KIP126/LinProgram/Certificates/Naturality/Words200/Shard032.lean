import KIP126.LinProgram.Generated.Naturality.Words200.Shard032
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard032
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard032
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
  exact ⟨Shared.RelationChunk000.relation6_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation104_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation232_zero, Shared.RelationChunk004.relation305_zero, Shared.RelationChunk004.relation307_zero, Shared.RelationChunk004.relation308_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk004.relation315_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk007.relation439_zero, Shared.RelationChunk007.relation440_zero, Shared.RelationChunk008.relation442_zero, Shared.RelationChunk008.relation444_zero, Shared.RelationChunk008.relation446_zero, Shared.RelationChunk008.relation447_zero, Shared.RelationChunk008.relation448_zero, Shared.RelationChunk008.relation453_zero, Shared.RelationChunk008.relation454_zero, Shared.RelationChunk008.relation455_zero, Shared.RelationChunk008.relation456_zero, Shared.RelationChunk008.relation458_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4098 128 := by cbv
private def targetRows : List BasisRow := [⟨37, 131, 0, "0,15,245,1"⟩,
  ⟨36, 131, 0, "0,15,246,1"⟩,
  ⟨32, 131, 0, "0,2,8,1,224,1"⟩,
  ⟨31, 131, 0, "0,2,8,1,225,1"⟩,
  ⟨27, 131, 0, "0,2,8,2,17,1,64,1"⟩,
  ⟨25, 131, 0, "345,1"⟩,
  ⟨25, 131, 1, "0,5,64,2"⟩,
  ⟨24, 131, 0, "8,2,160,1"⟩,
  ⟨24, 131, 1, "0,5,299,1"⟩,
  ⟨23, 131, 0, "8,1,232,1"⟩,
  ⟨22, 131, 0, "8,1,233,1"⟩,
  ⟨22, 131, 1, "0,5,301,1"⟩,
  ⟨22, 131, 2, "0,5,300,1"⟩,
  ⟨21, 131, 0, "9,1,219,1"⟩,
  ⟨21, 131, 1, "0,2,327,1"⟩,
  ⟨21, 131, 2, "0,3,317,1"⟩,
  ⟨17, 131, 0, "0,1,2,1,13,1,188,1"⟩,
  ⟨16, 131, 1, "1,1,328,1"⟩,
  ⟨15, 131, 0, "350,1"⟩,
  ⟨15, 131, 1, "349,1"⟩,
  ⟨15, 131, 2, "3,1,285,1"⟩,
  ⟨15, 131, 3, "2,2,287,1"⟩,
  ⟨14, 131, 0, "13,1,209,1"⟩,
  ⟨14, 131, 2, "0,4,312,1"⟩,
  ⟨14, 131, 3, "0,4,311,1"⟩,
  ⟨13, 131, 0, "67,1,75,1"⟩,
  ⟨13, 131, 2, "0,1,335,1"⟩,
  ⟨13, 131, 3, "0,4,314,1"⟩,
  ⟨12, 131, 0, "67,1,76,1"⟩,
  ⟨12, 131, 1, "0,1,336,1"⟩,
  ⟨12, 131, 2, "0,1,69,1,72,1"⟩,
  ⟨11, 131, 1, "0,1,337,1"⟩,
  ⟨11, 131, 2, "0,2,333,1"⟩,
  ⟨10, 131, 0, "0,1,338,1"⟩,
  ⟨8, 131, 0, "352,1"⟩,
  ⟨7, 131, 0, "353,1"⟩,
  ⟨7, 131, 1, "69,1,75,1"⟩,
  ⟨7, 131, 2, "0,1,339,1"⟩,
  ⟨6, 131, 1, "0,1,340,1"⟩,
  ⟨5, 131, 0, "0,3,69,2"⟩,
  ⟨4, 131, 0, "0,3,324,1"⟩,
  ⟨132, 132, 0, "0,132"⟩,
  ⟨43, 132, 0, "0,3,325,1"⟩,
  ⟨39, 132, 0, "16,1,183,1"⟩,
  ⟨38, 132, 0, "17,1,183,1"⟩,
  ⟨37, 132, 1, "0,16,246,1"⟩,
  ⟨36, 132, 0, "8,3,110,1"⟩,
  ⟨35, 132, 0, "8,3,111,1"⟩,
  ⟨34, 132, 0, "8,1,16,1,17,1,50,1"⟩,
  ⟨33, 132, 0, "8,2,161,1"⟩,
  ⟨32, 132, 0, "8,5,31,1"⟩,
  ⟨31, 132, 0, "8,4,16,1,17,1"⟩,
  ⟨30, 132, 1, "8,4,17,2"⟩,
  ⟨29, 132, 0, "8,1,238,1"⟩,
  ⟨29, 132, 1, "8,4,60,1"⟩,
  ⟨29, 132, 2, "0,1,343,1"⟩,
  ⟨28, 132, 0, "17,1,185,1"⟩,
  ⟨28, 132, 1, "8,6,13,1"⟩,
  ⟨27, 132, 0, "8,5,32,1"⟩,
  ⟨27, 132, 1, "0,1,344,1"⟩,
  ⟨26, 132, 1, "8,4,13,1,23,1"⟩,
  ⟨26, 132, 2, "0,6,64,2"⟩,
  ⟨25, 132, 0, "8,3,113,1"⟩,
  ⟨25, 132, 1, "8,3,13,1,51,1"⟩,
  ⟨25, 132, 2, "0,6,299,1"⟩,
  ⟨24, 132, 0, "8,2,162,1"⟩,
  ⟨24, 132, 1, "8,2,13,4"⟩,
  ⟨23, 132, 0, "8,1,23,1,113,1"⟩,
  ⟨23, 132, 1, "8,1,13,3,32,1"⟩,
  ⟨23, 132, 2, "0,6,301,1"⟩,
  ⟨23, 132, 3, "0,6,300,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2446_mem, Shared.BasisChunk002.row2447_mem, Shared.BasisChunk002.row2448_mem, Shared.BasisChunk002.row2449_mem, Shared.BasisChunk002.row2451_mem, Shared.BasisChunk002.row2453_mem, Shared.BasisChunk002.row2454_mem, Shared.BasisChunk002.row2455_mem, Shared.BasisChunk002.row2456_mem, Shared.BasisChunk002.row2457_mem, Shared.BasisChunk002.row2458_mem, Shared.BasisChunk002.row2459_mem, Shared.BasisChunk002.row2460_mem, Shared.BasisChunk002.row2461_mem, Shared.BasisChunk002.row2462_mem, Shared.BasisChunk002.row2463_mem, Shared.BasisChunk002.row2466_mem, Shared.BasisChunk002.row2468_mem, Shared.BasisChunk002.row2469_mem, Shared.BasisChunk002.row2470_mem, Shared.BasisChunk002.row2471_mem, Shared.BasisChunk002.row2472_mem, Shared.BasisChunk002.row2473_mem, Shared.BasisChunk002.row2475_mem, Shared.BasisChunk002.row2476_mem, Shared.BasisChunk002.row2477_mem, Shared.BasisChunk002.row2479_mem, Shared.BasisChunk002.row2480_mem, Shared.BasisChunk002.row2481_mem, Shared.BasisChunk002.row2482_mem, Shared.BasisChunk002.row2483_mem, Shared.BasisChunk002.row2485_mem, Shared.BasisChunk002.row2486_mem, Shared.BasisChunk002.row2487_mem, Shared.BasisChunk002.row2488_mem, Shared.BasisChunk002.row2489_mem, Shared.BasisChunk002.row2490_mem, Shared.BasisChunk002.row2491_mem, Shared.BasisChunk002.row2493_mem, Shared.BasisChunk002.row2494_mem, Shared.BasisChunk002.row2495_mem, Shared.BasisChunk002.row2496_mem, Shared.BasisChunk002.row2497_mem, Shared.BasisChunk002.row2499_mem, Shared.BasisChunk002.row2500_mem, Shared.BasisChunk002.row2502_mem, Shared.BasisChunk002.row2503_mem, Shared.BasisChunk002.row2504_mem, Shared.BasisChunk002.row2505_mem, Shared.BasisChunk002.row2506_mem, Shared.BasisChunk002.row2507_mem, Shared.BasisChunk002.row2508_mem, Shared.BasisChunk002.row2510_mem, Shared.BasisChunk002.row2512_mem, Shared.BasisChunk002.row2513_mem, Shared.BasisChunk002.row2514_mem, Shared.BasisChunk002.row2515_mem, Shared.BasisChunk002.row2516_mem, Shared.BasisChunk002.row2517_mem, Shared.BasisChunk002.row2518_mem, Shared.BasisChunk002.row2520_mem, Shared.BasisChunk002.row2521_mem, Shared.BasisChunk002.row2522_mem, Shared.BasisChunk002.row2523_mem, Shared.BasisChunk002.row2524_mem, Shared.BasisChunk002.row2525_mem, Shared.BasisChunk002.row2526_mem, Shared.BasisChunk002.row2527_mem, Shared.BasisChunk002.row2528_mem, Shared.BasisChunk002.row2529_mem, Shared.BasisChunk002.row2530_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard032
