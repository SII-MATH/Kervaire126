module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard075
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk025
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard075
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard075
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
  exact ⟨Shared.RelationChunk005.relation360_zero, Shared.RelationChunk005.relation361_zero, Shared.RelationChunk025.relation1098_zero, Shared.RelationChunk025.relation1099_zero, Shared.RelationChunk025.relation1102_zero, Shared.RelationChunk025.relation1103_zero, Shared.RelationChunk025.relation1104_zero, Shared.RelationChunk025.relation1105_zero, Shared.RelationChunk025.relation1106_zero, Shared.RelationChunk025.relation1107_zero, Shared.RelationChunk025.relation1108_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9602 128 := by cbv
private def targetRows : List BasisRow := [⟨6, 168, 1, "2,1,25,1,324,1"⟩,
  ⟨4, 168, 1, "2,2,18,1,324,1"⟩,
  ⟨169, 169, 0, "0,169"⟩,
  ⟨56, 169, 0, "1,1,721,1"⟩,
  ⟨53, 169, 0, "0,1,8,1,553,1"⟩,
  ⟨52, 169, 0, "0,1,8,1,554,1"⟩,
  ⟨45, 169, 0, "0,5,685,1"⟩,
  ⟨44, 169, 0, "0,4,17,1,403,1"⟩,
  ⟨43, 169, 0, "0,1,8,1,555,1"⟩,
  ⟨43, 169, 1, "0,5,686,1"⟩,
  ⟨42, 169, 0, "0,1,8,1,556,1"⟩,
  ⟨42, 169, 1, "0,2,722,1"⟩,
  ⟨42, 169, 2, "0,41,324,1"⟩,
  ⟨41, 169, 0, "0,1,17,1,433,1"⟩,
  ⟨36, 169, 0, "0,2,725,1"⟩,
  ⟨35, 169, 0, "752,1"⟩,
  ⟨33, 169, 0, "0,1,8,1,64,1,137,1"⟩,
  ⟨32, 169, 0, "0,1,8,1,64,1,138,1"⟩,
  ⟨32, 169, 1, "0,2,8,1,16,1,260,1"⟩,
  ⟨31, 169, 1, "0,2,8,1,17,1,260,1"⟩,
  ⟨26, 169, 1, "0,4,64,1,187,1"⟩,
  ⟨25, 169, 0, "1,1,727,1"⟩,
  ⟨25, 169, 1, "0,4,64,1,188,1"⟩,
  ⟨24, 169, 1, "0,4,703,1"⟩,
  ⟨23, 169, 0, "13,4,95,1"⟩,
  ⟨23, 169, 2, "0,3,717,1"⟩,
  ⟨23, 169, 3, "0,4,706,1"⟩,
  ⟨22, 169, 0, "13,3,164,1"⟩,
  ⟨22, 169, 1, "8,1,69,1,138,1"⟩,
  ⟨22, 169, 2, "0,1,3,1,646,1"⟩,
  ⟨22, 169, 3, "0,1,2,1,690,1"⟩,
  ⟨22, 169, 4, "0,5,693,1"⟩,
  ⟨21, 169, 0, "754,1"⟩,
  ⟨21, 169, 1, "1,1,728,1"⟩,
  ⟨21, 169, 2, "0,1,739,1"⟩,
  ⟨20, 169, 0, "1,1,3,1,639,1"⟩,
  ⟨20, 169, 1, "0,1,43,1,266,1"⟩,
  ⟨19, 169, 0, "1,1,729,1"⟩,
  ⟨19, 169, 1, "0,1,43,1,267,1"⟩,
  ⟨18, 169, 0, "8,2,69,1,80,1"⟩,
  ⟨18, 169, 1, "0,1,3,1,648,1"⟩,
  ⟨17, 169, 0, "75,1,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5762_mem, Shared.BasisChunk005.row5765_mem, Shared.BasisChunk005.row5767_mem, Shared.BasisChunk005.row5768_mem, Shared.BasisChunk005.row5769_mem, Shared.BasisChunk005.row5770_mem, Shared.BasisChunk005.row5771_mem, Shared.BasisChunk005.row5772_mem, Shared.BasisChunk005.row5773_mem, Shared.BasisChunk005.row5774_mem, Shared.BasisChunk005.row5775_mem, Shared.BasisChunk005.row5776_mem, Shared.BasisChunk005.row5777_mem, Shared.BasisChunk005.row5778_mem, Shared.BasisChunk005.row5779_mem, Shared.BasisChunk005.row5780_mem, Shared.BasisChunk005.row5782_mem, Shared.BasisChunk005.row5783_mem, Shared.BasisChunk005.row5784_mem, Shared.BasisChunk005.row5786_mem, Shared.BasisChunk005.row5789_mem, Shared.BasisChunk005.row5790_mem, Shared.BasisChunk005.row5791_mem, Shared.BasisChunk005.row5793_mem, Shared.BasisChunk005.row5794_mem, Shared.BasisChunk005.row5796_mem, Shared.BasisChunk005.row5797_mem, Shared.BasisChunk005.row5798_mem, Shared.BasisChunk005.row5799_mem, Shared.BasisChunk005.row5800_mem, Shared.BasisChunk005.row5801_mem, Shared.BasisChunk005.row5802_mem, Shared.BasisChunk005.row5803_mem, Shared.BasisChunk005.row5804_mem, Shared.BasisChunk005.row5805_mem, Shared.BasisChunk005.row5806_mem, Shared.BasisChunk005.row5807_mem, Shared.BasisChunk005.row5808_mem, Shared.BasisChunk005.row5809_mem, Shared.BasisChunk005.row5810_mem, Shared.BasisChunk005.row5811_mem, Shared.BasisChunk005.row5812_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard075
