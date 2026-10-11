module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard033
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard033
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard033
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
  exact ⟨Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk004.relation306_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk008.relation452_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4226 128 := by cbv
private def targetRows : List BasisRow := [⟨22, 132, 0, "13,4,23,1"⟩,
  ⟨22, 132, 1, "8,2,9,1,101,1"⟩,
  ⟨22, 132, 2, "0,4,317,1"⟩,
  ⟨21, 132, 0, "13,4,24,1"⟩,
  ⟨21, 132, 1, "8,1,9,1,13,1,80,1"⟩,
  ⟨20, 132, 1, "9,1,23,1,101,1"⟩,
  ⟨19, 132, 0, "16,1,188,1"⟩,
  ⟨19, 132, 2, "0,1,347,1"⟩,
  ⟨19, 132, 3, "0,1,346,1"⟩,
  ⟨18, 132, 0, "356,1"⟩,
  ⟨18, 132, 1, "355,1"⟩,
  ⟨18, 132, 2, "17,1,188,1"⟩,
  ⟨17, 132, 0, "358,1"⟩,
  ⟨16, 132, 2, "0,1,349,1"⟩,
  ⟨16, 132, 3, "0,1,3,1,285,1"⟩,
  ⟨15, 132, 1, "0,5,312,1"⟩,
  ⟨15, 132, 2, "0,5,311,1"⟩,
  ⟨14, 132, 0, "362,1"⟩,
  ⟨14, 132, 2, "0,2,335,1"⟩,
  ⟨14, 132, 3, "0,5,314,1"⟩,
  ⟨13, 132, 0, "13,1,213,1"⟩,
  ⟨13, 132, 1, "7,1,250,1"⟩,
  ⟨13, 132, 3, "0,2,336,1"⟩,
  ⟨13, 132, 4, "0,2,69,1,72,1"⟩,
  ⟨12, 132, 0, "364,1"⟩,
  ⟨12, 132, 2, "0,1,351,1"⟩,
  ⟨12, 132, 3, "0,2,337,1"⟩,
  ⟨12, 132, 4, "0,3,333,1"⟩,
  ⟨11, 132, 0, "365,1"⟩,
  ⟨9, 132, 1, "0,1,352,1"⟩,
  ⟨8, 132, 0, "367,1"⟩,
  ⟨7, 132, 0, "0,2,340,1"⟩,
  ⟨6, 132, 1, "0,4,69,2"⟩,
  ⟨5, 132, 0, "0,4,324,1"⟩,
  ⟨3, 132, 0, "2,1,69,2"⟩,
  ⟨2, 132, 0, "2,1,324,1"⟩,
  ⟨133, 133, 0, "0,133"⟩,
  ⟨44, 133, 0, "1,1,342,1"⟩,
  ⟨41, 133, 0, "0,1,8,1,236,1"⟩,
  ⟨40, 133, 0, "0,1,16,1,183,1"⟩,
  ⟨39, 133, 0, "0,1,17,1,183,1"⟩,
  ⟨38, 133, 0, "0,17,246,1"⟩,
  ⟨31, 133, 0, "0,1,8,1,237,1"⟩,
  ⟨30, 133, 0, "0,1,8,1,238,1"⟩,
  ⟨30, 133, 1, "0,2,343,1"⟩,
  ⟨29, 133, 0, "0,1,17,1,185,1"⟩,
  ⟨27, 133, 0, "0,7,64,2"⟩,
  ⟨26, 133, 0, "0,7,299,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2531_mem, Shared.BasisChunk002.row2532_mem, Shared.BasisChunk002.row2533_mem, Shared.BasisChunk002.row2534_mem, Shared.BasisChunk002.row2535_mem, Shared.BasisChunk002.row2537_mem, Shared.BasisChunk002.row2538_mem, Shared.BasisChunk002.row2540_mem, Shared.BasisChunk002.row2541_mem, Shared.BasisChunk002.row2542_mem, Shared.BasisChunk002.row2543_mem, Shared.BasisChunk002.row2544_mem, Shared.BasisChunk002.row2545_mem, Shared.BasisChunk002.row2549_mem, Shared.BasisChunk002.row2550_mem, Shared.BasisChunk002.row2552_mem, Shared.BasisChunk002.row2553_mem, Shared.BasisChunk002.row2554_mem, Shared.BasisChunk002.row2556_mem, Shared.BasisChunk002.row2557_mem, Shared.BasisChunk002.row2558_mem, Shared.BasisChunk002.row2559_mem, Shared.BasisChunk002.row2561_mem, Shared.BasisChunk002.row2562_mem, Shared.BasisChunk002.row2563_mem, Shared.BasisChunk002.row2565_mem, Shared.BasisChunk002.row2566_mem, Shared.BasisChunk002.row2567_mem, Shared.BasisChunk002.row2568_mem, Shared.BasisChunk002.row2570_mem, Shared.BasisChunk002.row2571_mem, Shared.BasisChunk002.row2572_mem, Shared.BasisChunk002.row2574_mem, Shared.BasisChunk002.row2575_mem, Shared.BasisChunk002.row2577_mem, Shared.BasisChunk002.row2579_mem, Shared.BasisChunk002.row2580_mem, Shared.BasisChunk002.row2581_mem, Shared.BasisChunk002.row2582_mem, Shared.BasisChunk002.row2583_mem, Shared.BasisChunk002.row2584_mem, Shared.BasisChunk002.row2585_mem, Shared.BasisChunk002.row2586_mem, Shared.BasisChunk002.row2587_mem, Shared.BasisChunk002.row2588_mem, Shared.BasisChunk002.row2589_mem, Shared.BasisChunk002.row2590_mem, Shared.BasisChunk002.row2591_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard033
