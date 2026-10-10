import KIP126.LinProgram.Generated.Naturality.Words200.Shard076
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard076
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard076
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
  exact ⟨Shared.RelationChunk000.relation41_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk002.relation247_zero, Shared.RelationChunk003.relation262_zero, Shared.RelationChunk008.relation474_zero, Shared.RelationChunk008.relation475_zero, Shared.RelationChunk008.relation476_zero, Shared.RelationChunk008.relation477_zero, Shared.RelationChunk008.relation478_zero, Shared.RelationChunk008.relation479_zero, Shared.RelationChunk008.relation480_zero, Shared.RelationChunk013.relation670_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk015.relation782_zero, Shared.RelationChunk015.relation783_zero, Shared.RelationChunk015.relation784_zero, Shared.RelationChunk015.relation785_zero, Shared.RelationChunk023.relation1032_zero, Shared.RelationChunk023.relation1033_zero, Shared.RelationChunk025.relation1091_zero, Shared.RelationChunk025.relation1092_zero, Shared.RelationChunk025.relation1093_zero, Shared.RelationChunk025.relation1094_zero, Shared.RelationChunk025.relation1095_zero, Shared.RelationChunk026.relation1117_zero, Shared.RelationChunk026.relation1118_zero, Shared.RelationChunk026.relation1119_zero, Shared.RelationChunk026.relation1121_zero, Shared.RelationChunk026.relation1122_zero, Shared.RelationChunk026.relation1123_zero, Shared.RelationChunk026.relation1126_zero, Shared.RelationChunk026.relation1127_zero, Shared.RelationChunk026.relation1128_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9730 128 := by cbv
private def targetRows : List BasisRow := [⟨17, 169, 1, "1,2,708,1"⟩,
  ⟨17, 169, 2, "0,1,8,2,367,1"⟩,
  ⟨17, 169, 3, "0,1,3,1,650,1"⟩,
  ⟨16, 169, 0, "75,1,189,1"⟩,
  ⟨16, 169, 1, "0,1,741,1"⟩,
  ⟨16, 169, 2, "0,1,67,1,197,1"⟩,
  ⟨15, 169, 1, "23,1,373,1"⟩,
  ⟨15, 169, 2, "0,1,30,1,324,1"⟩,
  ⟨15, 169, 3, "0,7,676,1"⟩,
  ⟨14, 169, 0, "75,1,190,1"⟩,
  ⟨14, 169, 1, "23,1,376,1"⟩,
  ⟨14, 169, 2, "0,2,732,1"⟩,
  ⟨14, 169, 3, "0,3,719,1"⟩,
  ⟨13, 169, 2, "0,5,696,1"⟩,
  ⟨12, 169, 0, "1,1,734,1"⟩,
  ⟨12, 169, 1, "1,1,7,1,571,1"⟩,
  ⟨12, 169, 2, "0,1,743,1"⟩,
  ⟨12, 169, 3, "0,2,18,1,414,1"⟩,
  ⟨12, 169, 4, "0,5,23,1,324,1"⟩,
  ⟨11, 169, 1, "3,1,18,1,333,1"⟩,
  ⟨11, 169, 2, "2,1,18,1,373,1"⟩,
  ⟨11, 169, 3, "0,1,746,1"⟩,
  ⟨11, 169, 4, "0,2,18,1,415,1"⟩,
  ⟨11, 169, 5, "0,2,8,1,9,1,324,1"⟩,
  ⟨11, 169, 6, "0,3,720,1"⟩,
  ⟨11, 169, 7, "0,9,18,1,324,1"⟩,
  ⟨10, 169, 0, "757,1"⟩,
  ⟨10, 169, 1, "756,1"⟩,
  ⟨10, 169, 2, "3,1,659,1"⟩,
  ⟨10, 169, 3, "2,1,18,1,376,1"⟩,
  ⟨10, 169, 4, "0,2,29,1,324,1"⟩,
  ⟨9, 169, 0, "0,1,2,1,698,1"⟩,
  ⟨8, 169, 0, "0,1,748,1"⟩,
  ⟨8, 169, 1, "0,1,747,1"⟩,
  ⟨7, 169, 0, "2,2,660,1"⟩,
  ⟨7, 169, 1, "0,1,749,1"⟩,
  ⟨6, 169, 0, "0,1,750,1"⟩,
  ⟨5, 169, 0, "0,1,751,1"⟩,
  ⟨4, 169, 0, "0,1,3,1,18,1,324,1"⟩,
  ⟨170, 170, 0, "0,170"⟩,
  ⟨54, 170, 0, "0,2,8,1,553,1"⟩,
  ⟨53, 170, 0, "0,2,8,1,554,1"⟩,
  ⟨46, 170, 0, "0,6,685,1"⟩,
  ⟨45, 170, 0, "0,5,17,1,403,1"⟩,
  ⟨44, 170, 0, "0,2,8,1,555,1"⟩,
  ⟨44, 170, 1, "0,6,686,1"⟩,
  ⟨43, 170, 0, "0,2,8,1,556,1"⟩,
  ⟨43, 170, 1, "0,3,722,1"⟩,
  ⟨43, 170, 2, "0,42,324,1"⟩,
  ⟨39, 170, 0, "17,1,452,1"⟩,
  ⟨38, 170, 0, "49,1,245,1"⟩,
  ⟨37, 170, 0, "8,1,572,1"⟩,
  ⟨37, 170, 1, "0,3,725,1"⟩,
  ⟨36, 170, 0, "8,3,244,1"⟩,
  ⟨36, 170, 1, "0,1,752,1"⟩,
  ⟨35, 170, 0, "8,1,16,1,17,1,149,1"⟩,
  ⟨34, 170, 1, "8,3,245,1"⟩,
  ⟨33, 170, 0, "8,3,247,1"⟩,
  ⟨33, 170, 1, "0,2,8,1,64,1,138,1"⟩,
  ⟨32, 170, 0, "8,4,166,1"⟩,
  ⟨31, 170, 0, "8,4,167,1"⟩,
  ⟨30, 170, 0, "64,1,206,1"⟩,
  ⟨30, 170, 1, "8,2,380,1"⟩,
  ⟨30, 170, 2, "8,3,248,1"⟩,
  ⟨29, 170, 0, "113,1,149,1"⟩,
  ⟨29, 170, 1, "8,1,17,1,278,1"⟩,
  ⟨29, 170, 2, "8,2,13,1,219,1"⟩,
  ⟨28, 170, 0, "17,1,454,1"⟩,
  ⟨28, 170, 1, "8,1,573,1"⟩,
  ⟨28, 170, 2, "8,1,13,2,194,1"⟩,
  ⟨27, 170, 0, "42,1,278,1"⟩,
  ⟨27, 170, 3, "0,1,753,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5813_mem, Shared.BasisChunk005.row5814_mem, Shared.BasisChunk005.row5815_mem, Shared.BasisChunk005.row5816_mem, Shared.BasisChunk005.row5817_mem, Shared.BasisChunk005.row5818_mem, Shared.BasisChunk005.row5820_mem, Shared.BasisChunk005.row5821_mem, Shared.BasisChunk005.row5822_mem, Shared.BasisChunk005.row5823_mem, Shared.BasisChunk005.row5824_mem, Shared.BasisChunk005.row5825_mem, Shared.BasisChunk005.row5826_mem, Shared.BasisChunk005.row5829_mem, Shared.BasisChunk005.row5830_mem, Shared.BasisChunk005.row5831_mem, Shared.BasisChunk005.row5832_mem, Shared.BasisChunk005.row5833_mem, Shared.BasisChunk005.row5834_mem, Shared.BasisChunk005.row5836_mem, Shared.BasisChunk005.row5837_mem, Shared.BasisChunk005.row5838_mem, Shared.BasisChunk005.row5839_mem, Shared.BasisChunk005.row5840_mem, Shared.BasisChunk005.row5841_mem, Shared.BasisChunk005.row5842_mem, Shared.BasisChunk005.row5843_mem, Shared.BasisChunk005.row5844_mem, Shared.BasisChunk005.row5845_mem, Shared.BasisChunk005.row5846_mem, Shared.BasisChunk005.row5847_mem, Shared.BasisChunk005.row5848_mem, Shared.BasisChunk005.row5849_mem, Shared.BasisChunk005.row5850_mem, Shared.BasisChunk005.row5851_mem, Shared.BasisChunk005.row5852_mem, Shared.BasisChunk005.row5853_mem, Shared.BasisChunk005.row5854_mem, Shared.BasisChunk005.row5855_mem, Shared.BasisChunk005.row5856_mem, Shared.BasisChunk005.row5858_mem, Shared.BasisChunk005.row5859_mem, Shared.BasisChunk005.row5861_mem, Shared.BasisChunk005.row5862_mem, Shared.BasisChunk005.row5863_mem, Shared.BasisChunk005.row5864_mem, Shared.BasisChunk005.row5865_mem, Shared.BasisChunk005.row5866_mem, Shared.BasisChunk005.row5867_mem, Shared.BasisChunk005.row5869_mem, Shared.BasisChunk005.row5870_mem, Shared.BasisChunk005.row5871_mem, Shared.BasisChunk005.row5872_mem, Shared.BasisChunk005.row5873_mem, Shared.BasisChunk005.row5874_mem, Shared.BasisChunk005.row5875_mem, Shared.BasisChunk005.row5877_mem, Shared.BasisChunk005.row5878_mem, Shared.BasisChunk005.row5879_mem, Shared.BasisChunk005.row5880_mem, Shared.BasisChunk005.row5881_mem, Shared.BasisChunk005.row5882_mem, Shared.BasisChunk005.row5883_mem, Shared.BasisChunk005.row5884_mem, Shared.BasisChunk005.row5885_mem, Shared.BasisChunk005.row5886_mem, Shared.BasisChunk005.row5887_mem, Shared.BasisChunk005.row5888_mem, Shared.BasisChunk005.row5889_mem, Shared.BasisChunk005.row5890_mem, Shared.BasisChunk005.row5891_mem, Shared.BasisChunk005.row5894_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard076
