import KIP126.LinProgram.Generated.Naturality.Words200.Shard037
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard037
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard037
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
  exact ⟨Shared.RelationChunk000.relation22_zero, Shared.RelationChunk004.relation303_zero, Shared.RelationChunk004.relation304_zero, Shared.RelationChunk008.relation467_zero, Shared.RelationChunk009.relation499_zero, Shared.RelationChunk009.relation500_zero, Shared.RelationChunk009.relation502_zero, Shared.RelationChunk009.relation503_zero, Shared.RelationChunk009.relation504_zero, Shared.RelationChunk009.relation510_zero, Shared.RelationChunk009.relation511_zero, Shared.RelationChunk009.relation512_zero, Shared.RelationChunk009.relation513_zero, Shared.RelationChunk009.relation514_zero, Shared.RelationChunk009.relation515_zero, Shared.RelationChunk009.relation516_zero, Shared.RelationChunk009.relation517_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4738 128 := by cbv
private def targetRows : List BasisRow := [⟨21, 136, 0, "0,4,358,1"⟩,
  ⟨20, 136, 0, "0,1,8,1,255,1"⟩,
  ⟨20, 136, 1, "0,1,2,1,346,1"⟩,
  ⟨20, 136, 2, "0,4,359,1"⟩,
  ⟨20, 136, 3, "0,5,349,1"⟩,
  ⟨19, 136, 0, "13,3,67,1"⟩,
  ⟨19, 136, 1, "2,1,355,1"⟩,
  ⟨19, 136, 2, "0,1,405,1"⟩,
  ⟨19, 136, 3, "0,1,20,1,188,1"⟩,
  ⟨18, 136, 0, "9,1,13,2,75,1"⟩,
  ⟨18, 136, 2, "1,2,359,1"⟩,
  ⟨17, 136, 0, "2,1,359,1"⟩,
  ⟨16, 136, 1, "3,2,267,1"⟩,
  ⟨15, 136, 0, "7,1,267,1"⟩,
  ⟨14, 136, 0, "0,1,407,1"⟩,
  ⟨13, 136, 2, "0,2,386,1"⟩,
  ⟨12, 136, 1, "0,1,410,1"⟩,
  ⟨12, 136, 2, "0,1,409,1"⟩,
  ⟨12, 136, 3, "0,2,389,1"⟩,
  ⟨12, 136, 4, "0,4,367,1"⟩,
  ⟨11, 136, 1, "1,1,389,1"⟩,
  ⟨11, 136, 2, "1,1,388,1"⟩,
  ⟨11, 136, 3, "0,2,391,1"⟩,
  ⟨11, 136, 4, "0,3,375,1"⟩,
  ⟨10, 136, 1, "0,1,414,1"⟩,
  ⟨10, 136, 2, "0,2,394,1"⟩,
  ⟨10, 136, 3, "0,2,392,1"⟩,
  ⟨10, 136, 4, "0,8,69,2"⟩,
  ⟨9, 136, 0, "1,1,393,1"⟩,
  ⟨9, 136, 1, "1,1,392,1"⟩,
  ⟨9, 136, 2, "0,1,415,1"⟩,
  ⟨9, 136, 3, "0,2,396,1"⟩,
  ⟨9, 136, 4, "0,8,324,1"⟩,
  ⟨8, 136, 0, "3,1,68,1,69,1"⟩,
  ⟨7, 136, 0, "2,1,368,1"⟩,
  ⟨6, 136, 0, "69,1,93,1"⟩,
  ⟨4, 136, 0, "2,2,69,2"⟩,
  ⟨3, 136, 1, "2,2,324,1"⟩,
  ⟨137, 137, 0, "0,137"⟩,
  ⟨46, 137, 0, "0,1,416,1"⟩,
  ⟨43, 137, 0, "0,5,17,1,183,1"⟩,
  ⟨42, 137, 0, "0,2,8,1,252,1"⟩,
  ⟨42, 137, 1, "0,21,246,1"⟩,
  ⟨41, 137, 0, "0,2,8,1,253,1"⟩,
  ⟨36, 137, 0, "0,2,402,1"⟩,
  ⟨35, 137, 1, "0,2,403,1"⟩,
  ⟨32, 137, 0, "0,2,8,1,16,1,137,1"⟩,
  ⟨31, 137, 0, "0,2,8,1,16,1,138,1"⟩,
  ⟨28, 137, 2, "0,11,300,1"⟩,
  ⟨27, 137, 0, "17,1,206,1"⟩,
  ⟨27, 137, 1, "0,9,317,1"⟩,
  ⟨26, 137, 0, "8,1,258,1"⟩,
  ⟨25, 137, 0, "8,1,259,1"⟩,
  ⟨25, 137, 1, "0,3,380,1"⟩,
  ⟨24, 137, 0, "8,2,180,1"⟩,
  ⟨24, 137, 1, "0,6,347,1"⟩,
  ⟨23, 137, 0, "8,1,9,1,167,1"⟩,
  ⟨23, 137, 1, "0,5,17,1,188,1"⟩,
  ⟨22, 137, 0, "9,1,248,1"⟩,
  ⟨21, 137, 0, "0,2,8,1,255,1"⟩,
  ⟨21, 137, 1, "0,5,359,1"⟩,
  ⟨21, 137, 2, "0,6,349,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2824_mem, Shared.BasisChunk002.row2825_mem, Shared.BasisChunk002.row2826_mem, Shared.BasisChunk002.row2827_mem, Shared.BasisChunk002.row2828_mem, Shared.BasisChunk002.row2829_mem, Shared.BasisChunk002.row2830_mem, Shared.BasisChunk002.row2831_mem, Shared.BasisChunk002.row2832_mem, Shared.BasisChunk002.row2833_mem, Shared.BasisChunk002.row2835_mem, Shared.BasisChunk002.row2836_mem, Shared.BasisChunk002.row2838_mem, Shared.BasisChunk002.row2839_mem, Shared.BasisChunk002.row2841_mem, Shared.BasisChunk002.row2844_mem, Shared.BasisChunk002.row2846_mem, Shared.BasisChunk002.row2847_mem, Shared.BasisChunk002.row2848_mem, Shared.BasisChunk002.row2849_mem, Shared.BasisChunk002.row2851_mem, Shared.BasisChunk002.row2852_mem, Shared.BasisChunk002.row2853_mem, Shared.BasisChunk002.row2854_mem, Shared.BasisChunk002.row2856_mem, Shared.BasisChunk002.row2857_mem, Shared.BasisChunk002.row2858_mem, Shared.BasisChunk002.row2859_mem, Shared.BasisChunk002.row2860_mem, Shared.BasisChunk002.row2861_mem, Shared.BasisChunk002.row2862_mem, Shared.BasisChunk002.row2863_mem, Shared.BasisChunk002.row2864_mem, Shared.BasisChunk002.row2865_mem, Shared.BasisChunk002.row2866_mem, Shared.BasisChunk002.row2867_mem, Shared.BasisChunk002.row2868_mem, Shared.BasisChunk002.row2870_mem, Shared.BasisChunk002.row2872_mem, Shared.BasisChunk002.row2873_mem, Shared.BasisChunk002.row2874_mem, Shared.BasisChunk002.row2875_mem, Shared.BasisChunk002.row2876_mem, Shared.BasisChunk002.row2877_mem, Shared.BasisChunk002.row2878_mem, Shared.BasisChunk002.row2880_mem, Shared.BasisChunk002.row2881_mem, Shared.BasisChunk002.row2882_mem, Shared.BasisChunk002.row2885_mem, Shared.BasisChunk002.row2886_mem, Shared.BasisChunk002.row2887_mem, Shared.BasisChunk002.row2888_mem, Shared.BasisChunk002.row2889_mem, Shared.BasisChunk002.row2890_mem, Shared.BasisChunk002.row2891_mem, Shared.BasisChunk002.row2892_mem, Shared.BasisChunk002.row2893_mem, Shared.BasisChunk002.row2894_mem, Shared.BasisChunk002.row2895_mem, Shared.BasisChunk002.row2897_mem, Shared.BasisChunk002.row2898_mem, Shared.BasisChunk002.row2899_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard037
