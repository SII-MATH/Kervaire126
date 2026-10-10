import KIP126.LinProgram.Generated.Naturality.Words200.Shard035
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard035
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard035
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation34_zero, Shared.RelationChunk000.relation38_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation71_zero, Shared.RelationChunk000.relation72_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation154_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk001.relation184_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk002.relation233_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk002.relation239_zero, Shared.RelationChunk002.relation240_zero, Shared.RelationChunk002.relation241_zero, Shared.RelationChunk002.relation242_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk004.relation295_zero, Shared.RelationChunk004.relation296_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk005.relation326_zero, Shared.RelationChunk005.relation327_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk005.relation331_zero, Shared.RelationChunk005.relation332_zero, Shared.RelationChunk005.relation333_zero, Shared.RelationChunk008.relation450_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk008.relation463_zero, Shared.RelationChunk008.relation464_zero, Shared.RelationChunk008.relation465_zero, Shared.RelationChunk008.relation466_zero, Shared.RelationChunk008.relation470_zero, Shared.RelationChunk009.relation496_zero, Shared.RelationChunk009.relation497_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4482 128 := by cbv
private def targetRows : List BasisRow := [⟨19, 134, 0, "381,1"⟩,
  ⟨19, 134, 1, "0,2,358,1"⟩,
  ⟨18, 134, 1, "1,1,357,1"⟩,
  ⟨18, 134, 2, "0,2,359,1"⟩,
  ⟨18, 134, 3, "0,3,349,1"⟩,
  ⟨17, 134, 2, "0,1,2,1,328,1"⟩,
  ⟨17, 134, 3, "0,7,312,1"⟩,
  ⟨16, 134, 0, "8,1,250,1"⟩,
  ⟨16, 134, 1, "1,1,360,1"⟩,
  ⟨15, 134, 0, "384,1"⟩,
  ⟨15, 134, 1, "1,1,361,1"⟩,
  ⟨15, 134, 2, "0,1,370,1"⟩,
  ⟨14, 134, 1, "0,2,363,1"⟩,
  ⟨13, 134, 0, "0,2,365,1"⟩,
  ⟨12, 134, 0, "18,1,188,1"⟩,
  ⟨12, 134, 1, "0,1,371,1"⟩,
  ⟨12, 134, 2, "0,1,69,1,79,1"⟩,
  ⟨11, 134, 2, "18,1,189,1"⟩,
  ⟨11, 134, 3, "0,1,69,1,80,1"⟩,
  ⟨11, 134, 4, "0,2,366,1"⟩,
  ⟨10, 134, 2, "1,1,366,1"⟩,
  ⟨10, 134, 3, "0,1,373,1"⟩,
  ⟨10, 134, 4, "0,2,367,1"⟩,
  ⟨9, 134, 0, "391,1"⟩,
  ⟨9, 134, 1, "390,1"⟩,
  ⟨9, 134, 2, "69,1,82,1"⟩,
  ⟨9, 134, 3, "18,1,190,1"⟩,
  ⟨9, 134, 4, "0,1,375,1"⟩,
  ⟨8, 134, 0, "395,1"⟩,
  ⟨8, 134, 1, "394,1"⟩,
  ⟨8, 134, 4, "69,1,85,1"⟩,
  ⟨8, 134, 5, "0,6,69,2"⟩,
  ⟨7, 134, 0, "397,1"⟩,
  ⟨7, 134, 1, "396,1"⟩,
  ⟨7, 134, 2, "1,1,368,1"⟩,
  ⟨7, 134, 3, "0,1,377,1"⟩,
  ⟨7, 134, 4, "0,6,324,1"⟩,
  ⟨6, 134, 0, "399,1"⟩,
  ⟨6, 134, 1, "398,1"⟩,
  ⟨6, 134, 2, "2,1,340,1"⟩,
  ⟨6, 134, 3, "0,1,378,1"⟩,
  ⟨5, 134, 0, "400,1"⟩,
  ⟨5, 134, 1, "2,1,341,1"⟩,
  ⟨5, 134, 2, "0,2,2,1,69,2"⟩,
  ⟨4, 134, 0, "0,2,2,1,324,1"⟩,
  ⟨135, 135, 0, "0,135"⟩,
  ⟨41, 135, 0, "0,3,17,1,183,1"⟩,
  ⟨40, 135, 1, "0,19,246,1"⟩,
  ⟨39, 135, 0, "8,1,253,1"⟩,
  ⟨38, 135, 0, "17,1,200,1"⟩,
  ⟨37, 135, 0, "401,1"⟩,
  ⟨36, 135, 0, "8,3,116,1"⟩,
  ⟨35, 135, 0, "8,3,117,1"⟩,
  ⟨34, 135, 1, "8,2,17,1,78,1"⟩,
  ⟨33, 135, 0, "403,1"⟩,
  ⟨33, 135, 1, "8,2,171,1"⟩,
  ⟨32, 135, 0, "8,5,39,1"⟩,
  ⟨31, 135, 0, "8,5,40,1"⟩,
  ⟨30, 135, 1, "8,4,17,1,20,1"⟩,
  ⟨29, 135, 0, "8,1,16,1,138,1"⟩,
  ⟨29, 135, 1, "8,4,63,1"⟩,
  ⟨29, 135, 2, "0,1,8,1,244,1"⟩,
  ⟨28, 135, 0, "8,1,17,1,138,1"⟩,
  ⟨28, 135, 1, "8,5,9,1,13,1"⟩,
  ⟨27, 135, 1, "8,4,9,1,32,1"⟩,
  ⟨26, 135, 0, "8,3,9,1,13,1,23,1"⟩,
  ⟨26, 135, 1, "8,4,64,1"⟩,
  ⟨26, 135, 2, "0,9,300,1"⟩,
  ⟨25, 135, 0, "8,2,9,1,13,1,51,1"⟩,
  ⟨25, 135, 1, "8,3,118,1"⟩,
  ⟨25, 135, 2, "0,7,317,1"⟩,
  ⟨24, 135, 0, "8,1,9,1,13,4"⟩,
  ⟨24, 135, 1, "8,2,17,1,80,1"⟩,
  ⟨23, 135, 0, "9,1,13,3,32,1"⟩,
  ⟨23, 135, 1, "8,2,173,1"⟩,
  ⟨23, 135, 2, "0,1,380,1"⟩,
  ⟨22, 135, 1, "8,2,13,1,101,1"⟩,
  ⟨22, 135, 2, "0,4,347,1"⟩,
  ⟨21, 135, 0, "8,1,13,2,80,1"⟩,
  ⟨21, 135, 1, "0,3,17,1,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2664_mem, Shared.BasisChunk002.row2665_mem, Shared.BasisChunk002.row2667_mem, Shared.BasisChunk002.row2668_mem, Shared.BasisChunk002.row2669_mem, Shared.BasisChunk002.row2672_mem, Shared.BasisChunk002.row2673_mem, Shared.BasisChunk002.row2674_mem, Shared.BasisChunk002.row2675_mem, Shared.BasisChunk002.row2676_mem, Shared.BasisChunk002.row2677_mem, Shared.BasisChunk002.row2678_mem, Shared.BasisChunk002.row2680_mem, Shared.BasisChunk002.row2681_mem, Shared.BasisChunk002.row2682_mem, Shared.BasisChunk002.row2683_mem, Shared.BasisChunk002.row2684_mem, Shared.BasisChunk002.row2687_mem, Shared.BasisChunk002.row2688_mem, Shared.BasisChunk002.row2689_mem, Shared.BasisChunk002.row2692_mem, Shared.BasisChunk002.row2693_mem, Shared.BasisChunk002.row2694_mem, Shared.BasisChunk002.row2695_mem, Shared.BasisChunk002.row2696_mem, Shared.BasisChunk002.row2697_mem, Shared.BasisChunk002.row2698_mem, Shared.BasisChunk002.row2699_mem, Shared.BasisChunk002.row2700_mem, Shared.BasisChunk002.row2701_mem, Shared.BasisChunk002.row2704_mem, Shared.BasisChunk002.row2705_mem, Shared.BasisChunk002.row2706_mem, Shared.BasisChunk002.row2707_mem, Shared.BasisChunk002.row2708_mem, Shared.BasisChunk002.row2709_mem, Shared.BasisChunk002.row2710_mem, Shared.BasisChunk002.row2711_mem, Shared.BasisChunk002.row2712_mem, Shared.BasisChunk002.row2713_mem, Shared.BasisChunk002.row2714_mem, Shared.BasisChunk002.row2715_mem, Shared.BasisChunk002.row2716_mem, Shared.BasisChunk002.row2717_mem, Shared.BasisChunk002.row2718_mem, Shared.BasisChunk002.row2719_mem, Shared.BasisChunk002.row2720_mem, Shared.BasisChunk002.row2722_mem, Shared.BasisChunk002.row2723_mem, Shared.BasisChunk002.row2724_mem, Shared.BasisChunk002.row2725_mem, Shared.BasisChunk002.row2726_mem, Shared.BasisChunk002.row2727_mem, Shared.BasisChunk002.row2729_mem, Shared.BasisChunk002.row2730_mem, Shared.BasisChunk002.row2731_mem, Shared.BasisChunk002.row2732_mem, Shared.BasisChunk002.row2733_mem, Shared.BasisChunk002.row2735_mem, Shared.BasisChunk002.row2736_mem, Shared.BasisChunk002.row2737_mem, Shared.BasisChunk002.row2738_mem, Shared.BasisChunk002.row2739_mem, Shared.BasisChunk002.row2740_mem, Shared.BasisChunk002.row2742_mem, Shared.BasisChunk002.row2743_mem, Shared.BasisChunk002.row2744_mem, Shared.BasisChunk002.row2745_mem, Shared.BasisChunk002.row2746_mem, Shared.BasisChunk002.row2747_mem, Shared.BasisChunk002.row2748_mem, Shared.BasisChunk002.row2749_mem, Shared.BasisChunk002.row2750_mem, Shared.BasisChunk002.row2752_mem, Shared.BasisChunk002.row2753_mem, Shared.BasisChunk002.row2754_mem, Shared.BasisChunk002.row2756_mem, Shared.BasisChunk002.row2757_mem, Shared.BasisChunk002.row2758_mem, Shared.BasisChunk002.row2759_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard035
