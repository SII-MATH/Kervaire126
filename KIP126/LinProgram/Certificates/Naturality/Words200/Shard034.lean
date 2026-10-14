module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard034
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard034
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard034
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
  exact ⟨Shared.RelationChunk000.relation64_zero, Shared.RelationChunk003.relation287_zero, Shared.RelationChunk007.relation438_zero, Shared.RelationChunk008.relation459_zero, Shared.RelationChunk008.relation460_zero, Shared.RelationChunk008.relation461_zero, Shared.RelationChunk008.relation471_zero, Shared.RelationChunk008.relation472_zero, Shared.RelationChunk008.relation474_zero, Shared.RelationChunk008.relation475_zero, Shared.RelationChunk008.relation476_zero, Shared.RelationChunk008.relation477_zero, Shared.RelationChunk008.relation478_zero, Shared.RelationChunk008.relation479_zero, Shared.RelationChunk008.relation480_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4354 128 := by cbv
private def targetRows : List BasisRow := [⟨24, 133, 0, "0,7,300,1"⟩,
  ⟨23, 133, 1, "0,5,317,1"⟩,
  ⟨21, 133, 0, "0,1,16,1,187,1"⟩,
  ⟨20, 133, 0, "69,1,78,1"⟩,
  ⟨20, 133, 1, "0,1,16,1,188,1"⟩,
  ⟨20, 133, 2, "0,2,347,1"⟩,
  ⟨20, 133, 3, "0,2,346,1"⟩,
  ⟨19, 133, 1, "0,1,356,1"⟩,
  ⟨19, 133, 2, "0,1,355,1"⟩,
  ⟨19, 133, 3, "0,1,17,1,188,1"⟩,
  ⟨18, 133, 0, "0,1,358,1"⟩,
  ⟨17, 133, 0, "13,2,133,1"⟩,
  ⟨17, 133, 1, "0,1,359,1"⟩,
  ⟨17, 133, 2, "0,1,13,1,212,1"⟩,
  ⟨17, 133, 3, "0,2,349,1"⟩,
  ⟨16, 133, 1, "13,2,134,1"⟩,
  ⟨16, 133, 2, "2,1,328,1"⟩,
  ⟨16, 133, 3, "1,1,349,1"⟩,
  ⟨16, 133, 4, "0,6,312,1"⟩,
  ⟨15, 133, 0, "1,1,3,1,287,1"⟩,
  ⟨15, 133, 1, "0,6,314,1"⟩,
  ⟨14, 133, 0, "370,1"⟩,
  ⟨14, 133, 1, "0,3,69,1,72,1"⟩,
  ⟨13, 133, 0, "0,1,363,1"⟩,
  ⟨12, 133, 1, "0,1,365,1"⟩,
  ⟨11, 133, 0, "371,1"⟩,
  ⟨11, 133, 1, "69,1,79,1"⟩,
  ⟨10, 133, 0, "372,1"⟩,
  ⟨10, 133, 1, "69,1,80,1"⟩,
  ⟨10, 133, 2, "0,1,366,1"⟩,
  ⟨9, 133, 0, "374,1"⟩,
  ⟨9, 133, 1, "373,1"⟩,
  ⟨9, 133, 2, "0,1,367,1"⟩,
  ⟨7, 133, 0, "1,1,69,1,76,1"⟩,
  ⟨7, 133, 1, "0,5,69,2"⟩,
  ⟨6, 133, 1, "0,5,324,1"⟩,
  ⟨5, 133, 0, "378,1"⟩,
  ⟨4, 133, 0, "0,1,2,1,69,2"⟩,
  ⟨3, 133, 0, "0,1,2,1,324,1"⟩,
  ⟨134, 134, 0, "0,134"⟩,
  ⟨42, 134, 0, "0,2,8,1,236,1"⟩,
  ⟨41, 134, 0, "0,2,16,1,183,1"⟩,
  ⟨40, 134, 0, "0,2,17,1,183,1"⟩,
  ⟨39, 134, 0, "0,18,246,1"⟩,
  ⟨32, 134, 0, "0,2,8,1,237,1"⟩,
  ⟨31, 134, 0, "0,2,8,1,238,1"⟩,
  ⟨31, 134, 1, "0,3,343,1"⟩,
  ⟨27, 134, 0, "0,8,299,1"⟩,
  ⟨26, 134, 0, "8,1,245,1"⟩,
  ⟨25, 134, 0, "8,1,247,1"⟩,
  ⟨25, 134, 1, "0,8,300,1"⟩,
  ⟨24, 134, 0, "8,2,166,1"⟩,
  ⟨24, 134, 1, "0,6,317,1"⟩,
  ⟨23, 134, 0, "8,2,167,1"⟩,
  ⟨22, 134, 1, "8,1,248,1"⟩,
  ⟨21, 134, 0, "13,1,219,1"⟩,
  ⟨21, 134, 1, "0,2,16,1,188,1"⟩,
  ⟨21, 134, 2, "0,3,347,1"⟩,
  ⟨20, 134, 0, "13,1,220,1"⟩,
  ⟨20, 134, 1, "0,2,355,1"⟩,
  ⟨20, 134, 2, "0,2,17,1,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2592_mem, Shared.BasisChunk002.row2594_mem, Shared.BasisChunk002.row2595_mem, Shared.BasisChunk002.row2596_mem, Shared.BasisChunk002.row2597_mem, Shared.BasisChunk002.row2598_mem, Shared.BasisChunk002.row2599_mem, Shared.BasisChunk002.row2601_mem, Shared.BasisChunk002.row2602_mem, Shared.BasisChunk002.row2603_mem, Shared.BasisChunk002.row2604_mem, Shared.BasisChunk002.row2605_mem, Shared.BasisChunk002.row2606_mem, Shared.BasisChunk002.row2607_mem, Shared.BasisChunk002.row2608_mem, Shared.BasisChunk002.row2610_mem, Shared.BasisChunk002.row2611_mem, Shared.BasisChunk002.row2612_mem, Shared.BasisChunk002.row2613_mem, Shared.BasisChunk002.row2614_mem, Shared.BasisChunk002.row2615_mem, Shared.BasisChunk002.row2616_mem, Shared.BasisChunk002.row2617_mem, Shared.BasisChunk002.row2618_mem, Shared.BasisChunk002.row2620_mem, Shared.BasisChunk002.row2621_mem, Shared.BasisChunk002.row2622_mem, Shared.BasisChunk002.row2623_mem, Shared.BasisChunk002.row2624_mem, Shared.BasisChunk002.row2625_mem, Shared.BasisChunk002.row2626_mem, Shared.BasisChunk002.row2627_mem, Shared.BasisChunk002.row2628_mem, Shared.BasisChunk002.row2631_mem, Shared.BasisChunk002.row2632_mem, Shared.BasisChunk002.row2634_mem, Shared.BasisChunk002.row2635_mem, Shared.BasisChunk002.row2636_mem, Shared.BasisChunk002.row2637_mem, Shared.BasisChunk002.row2638_mem, Shared.BasisChunk002.row2640_mem, Shared.BasisChunk002.row2641_mem, Shared.BasisChunk002.row2642_mem, Shared.BasisChunk002.row2643_mem, Shared.BasisChunk002.row2645_mem, Shared.BasisChunk002.row2646_mem, Shared.BasisChunk002.row2647_mem, Shared.BasisChunk002.row2649_mem, Shared.BasisChunk002.row2650_mem, Shared.BasisChunk002.row2651_mem, Shared.BasisChunk002.row2652_mem, Shared.BasisChunk002.row2653_mem, Shared.BasisChunk002.row2654_mem, Shared.BasisChunk002.row2655_mem, Shared.BasisChunk002.row2657_mem, Shared.BasisChunk002.row2658_mem, Shared.BasisChunk002.row2659_mem, Shared.BasisChunk002.row2660_mem, Shared.BasisChunk002.row2661_mem, Shared.BasisChunk002.row2662_mem, Shared.BasisChunk002.row2663_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard034
