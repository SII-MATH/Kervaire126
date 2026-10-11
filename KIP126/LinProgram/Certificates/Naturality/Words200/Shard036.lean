module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard036
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard036
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard036
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
  exact ⟨Shared.RelationChunk008.relation482_zero, Shared.RelationChunk009.relation489_zero, Shared.RelationChunk009.relation490_zero, Shared.RelationChunk009.relation491_zero, Shared.RelationChunk009.relation492_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4610 128 := by cbv
private def targetRows : List BasisRow := [⟨20, 135, 0, "13,1,23,1,101,1"⟩,
  ⟨20, 135, 3, "0,3,358,1"⟩,
  ⟨19, 135, 0, "8,1,255,1"⟩,
  ⟨19, 135, 1, "2,1,346,1"⟩,
  ⟨19, 135, 2, "0,3,359,1"⟩,
  ⟨19, 135, 3, "0,4,349,1"⟩,
  ⟨18, 135, 0, "405,1"⟩,
  ⟨18, 135, 1, "20,1,188,1"⟩,
  ⟨17, 135, 0, "1,1,369,1"⟩,
  ⟨14, 135, 0, "406,1"⟩,
  ⟨13, 135, 1, "1,2,351,1"⟩,
  ⟨13, 135, 2, "0,2,69,1,79,1"⟩,
  ⟨12, 135, 0, "408,1"⟩,
  ⟨12, 135, 1, "0,1,386,1"⟩,
  ⟨12, 135, 2, "0,2,69,1,80,1"⟩,
  ⟨11, 135, 0, "411,1"⟩,
  ⟨11, 135, 1, "410,1"⟩,
  ⟨11, 135, 2, "409,1"⟩,
  ⟨11, 135, 3, "0,1,389,1"⟩,
  ⟨11, 135, 4, "0,3,367,1"⟩,
  ⟨10, 135, 2, "0,1,391,1"⟩,
  ⟨10, 135, 3, "0,1,390,1"⟩,
  ⟨10, 135, 4, "0,2,375,1"⟩,
  ⟨9, 135, 1, "1,1,376,1"⟩,
  ⟨9, 135, 3, "0,1,394,1"⟩,
  ⟨9, 135, 4, "0,1,392,1"⟩,
  ⟨9, 135, 5, "0,7,69,2"⟩,
  ⟨8, 135, 1, "2,1,353,1"⟩,
  ⟨8, 135, 2, "2,1,69,1,75,1"⟩,
  ⟨8, 135, 3, "0,1,397,1"⟩,
  ⟨8, 135, 4, "0,1,396,1"⟩,
  ⟨8, 135, 5, "0,2,377,1"⟩,
  ⟨8, 135, 6, "0,7,324,1"⟩,
  ⟨7, 135, 0, "2,1,69,1,76,1"⟩,
  ⟨7, 135, 1, "0,1,398,1"⟩,
  ⟨7, 135, 2, "0,2,378,1"⟩,
  ⟨136, 136, 0, "0,136"⟩,
  ⟨45, 136, 0, "416,1"⟩,
  ⟨42, 136, 0, "0,4,17,1,183,1"⟩,
  ⟨41, 136, 0, "0,1,8,1,252,1"⟩,
  ⟨41, 136, 1, "0,20,246,1"⟩,
  ⟨40, 136, 0, "0,1,8,1,253,1"⟩,
  ⟨39, 136, 0, "0,1,17,1,200,1"⟩,
  ⟨35, 136, 0, "0,1,402,1"⟩,
  ⟨34, 136, 0, "0,1,403,1"⟩,
  ⟨31, 136, 0, "0,1,8,1,16,1,137,1"⟩,
  ⟨30, 136, 0, "0,1,8,1,16,1,138,1"⟩,
  ⟨30, 136, 1, "0,2,8,1,244,1"⟩,
  ⟨29, 136, 0, "0,1,8,1,17,1,138,1"⟩,
  ⟨27, 136, 0, "0,10,300,1"⟩,
  ⟨26, 136, 0, "0,8,317,1"⟩,
  ⟨24, 136, 0, "0,2,380,1"⟩,
  ⟨23, 136, 0, "0,1,404,1"⟩,
  ⟨23, 136, 1, "0,5,347,1"⟩,
  ⟨22, 136, 0, "0,4,17,1,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2760_mem, Shared.BasisChunk002.row2763_mem, Shared.BasisChunk002.row2764_mem, Shared.BasisChunk002.row2765_mem, Shared.BasisChunk002.row2766_mem, Shared.BasisChunk002.row2767_mem, Shared.BasisChunk002.row2768_mem, Shared.BasisChunk002.row2769_mem, Shared.BasisChunk002.row2770_mem, Shared.BasisChunk002.row2771_mem, Shared.BasisChunk002.row2773_mem, Shared.BasisChunk002.row2774_mem, Shared.BasisChunk002.row2775_mem, Shared.BasisChunk002.row2776_mem, Shared.BasisChunk002.row2777_mem, Shared.BasisChunk002.row2778_mem, Shared.BasisChunk002.row2779_mem, Shared.BasisChunk002.row2780_mem, Shared.BasisChunk002.row2781_mem, Shared.BasisChunk002.row2782_mem, Shared.BasisChunk002.row2785_mem, Shared.BasisChunk002.row2786_mem, Shared.BasisChunk002.row2787_mem, Shared.BasisChunk002.row2789_mem, Shared.BasisChunk002.row2791_mem, Shared.BasisChunk002.row2792_mem, Shared.BasisChunk002.row2793_mem, Shared.BasisChunk002.row2795_mem, Shared.BasisChunk002.row2796_mem, Shared.BasisChunk002.row2797_mem, Shared.BasisChunk002.row2798_mem, Shared.BasisChunk002.row2799_mem, Shared.BasisChunk002.row2800_mem, Shared.BasisChunk002.row2801_mem, Shared.BasisChunk002.row2802_mem, Shared.BasisChunk002.row2803_mem, Shared.BasisChunk002.row2804_mem, Shared.BasisChunk002.row2806_mem, Shared.BasisChunk002.row2807_mem, Shared.BasisChunk002.row2808_mem, Shared.BasisChunk002.row2809_mem, Shared.BasisChunk002.row2810_mem, Shared.BasisChunk002.row2811_mem, Shared.BasisChunk002.row2812_mem, Shared.BasisChunk002.row2813_mem, Shared.BasisChunk002.row2814_mem, Shared.BasisChunk002.row2815_mem, Shared.BasisChunk002.row2816_mem, Shared.BasisChunk002.row2817_mem, Shared.BasisChunk002.row2818_mem, Shared.BasisChunk002.row2819_mem, Shared.BasisChunk002.row2820_mem, Shared.BasisChunk002.row2821_mem, Shared.BasisChunk002.row2822_mem, Shared.BasisChunk002.row2823_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard036
