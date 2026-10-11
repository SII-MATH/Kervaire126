module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard062
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard062
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard062
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation63_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk006.relation365_zero, Shared.RelationChunk006.relation366_zero, Shared.RelationChunk011.relation572_zero, Shared.RelationChunk011.relation573_zero, Shared.RelationChunk011.relation574_zero, Shared.RelationChunk011.relation576_zero, Shared.RelationChunk011.relation579_zero, Shared.RelationChunk011.relation580_zero, Shared.RelationChunk018.relation880_zero, Shared.RelationChunk019.relation883_zero, Shared.RelationChunk019.relation884_zero, Shared.RelationChunk019.relation885_zero, Shared.RelationChunk019.relation886_zero, Shared.RelationChunk019.relation887_zero, Shared.RelationChunk019.relation888_zero, Shared.RelationChunk019.relation889_zero, Shared.RelationChunk019.relation890_zero, Shared.RelationChunk019.relation892_zero, Shared.RelationChunk019.relation893_zero, Shared.RelationChunk019.relation894_zero, Shared.RelationChunk019.relation896_zero, Shared.RelationChunk019.relation898_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7938 128 := by cbv
private def targetRows : List BasisRow := [⟨26, 159, 0, "8,1,471,1"⟩,
  ⟨26, 159, 1, "8,2,13,2,101,1"⟩,
  ⟨26, 159, 2, "0,1,8,1,454,1"⟩,
  ⟨26, 159, 3, "0,5,586,1"⟩,
  ⟨25, 159, 0, "9,1,435,1"⟩,
  ⟨25, 159, 1, "8,1,13,3,80,1"⟩,
  ⟨25, 159, 2, "0,1,20,1,292,1"⟩,
  ⟨24, 159, 0, "13,2,23,1,101,1"⟩,
  ⟨24, 159, 1, "8,3,201,1"⟩,
  ⟨23, 159, 0, "8,2,9,1,188,1"⟩,
  ⟨22, 159, 0, "8,1,9,1,267,1"⟩,
  ⟨21, 159, 0, "9,1,23,1,188,1"⟩,
  ⟨21, 159, 1, "0,1,627,1"⟩,
  ⟨20, 159, 0, "23,1,286,1"⟩,
  ⟨20, 159, 1, "0,2,8,1,449,1"⟩,
  ⟨19, 159, 1, "23,1,287,1"⟩,
  ⟨19, 159, 2, "0,1,628,1"⟩,
  ⟨19, 159, 3, "0,7,575,1"⟩,
  ⟨18, 159, 0, "640,1"⟩,
  ⟨18, 159, 2, "1,2,604,1"⟩,
  ⟨18, 159, 3, "0,2,17,1,314,1"⟩,
  ⟨17, 159, 1, "1,1,618,1"⟩,
  ⟨17, 159, 3, "0,1,629,1"⟩,
  ⟨16, 159, 0, "17,1,333,1"⟩,
  ⟨16, 159, 1, "13,1,408,1"⟩,
  ⟨16, 159, 2, "0,1,630,1"⟩,
  ⟨15, 159, 0, "13,1,411,1"⟩,
  ⟨14, 159, 0, "1,1,621,1"⟩,
  ⟨13, 159, 0, "8,1,479,1"⟩,
  ⟨13, 159, 1, "0,1,7,1,486,1"⟩,
  ⟨12, 159, 0, "9,1,445,1"⟩,
  ⟨12, 159, 1, "1,1,7,1,478,1"⟩,
  ⟨12, 159, 2, "0,1,631,1"⟩,
  ⟨11, 159, 0, "18,1,311,1"⟩,
  ⟨11, 159, 1, "7,2,314,1"⟩,
  ⟨11, 159, 3, "0,1,16,1,69,2"⟩,
  ⟨10, 159, 0, "18,1,314,1"⟩,
  ⟨10, 159, 1, "0,1,17,1,69,2"⟩,
  ⟨10, 159, 2, "0,1,16,1,324,1"⟩,
  ⟨9, 159, 0, "0,1,17,1,324,1"⟩,
  ⟨160, 160, 0, "0,160"⟩,
  ⟨53, 160, 0, "641,1"⟩,
  ⟨50, 160, 0, "0,4,17,1,296,1"⟩,
  ⟨49, 160, 0, "0,1,8,1,469,1"⟩,
  ⟨49, 160, 1, "0,4,606,1"⟩,
  ⟨48, 160, 0, "0,1,8,1,470,1"⟩,
  ⟨47, 160, 0, "0,1,17,1,326,1"⟩,
  ⟨43, 160, 0, "0,1,635,1"⟩,
  ⟨42, 160, 0, "0,1,636,1"⟩,
  ⟨39, 160, 0, "0,1,8,1,16,1,224,1"⟩,
  ⟨38, 160, 0, "0,1,8,1,16,1,225,1"⟩,
  ⟨38, 160, 1, "0,2,8,1,452,1"⟩,
  ⟨37, 160, 0, "0,1,8,1,17,1,225,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4793_mem, Shared.BasisChunk004.row4794_mem, Shared.BasisChunk004.row4795_mem, Shared.BasisChunk004.row4796_mem, Shared.BasisChunk004.row4797_mem, Shared.BasisChunk004.row4798_mem, Shared.BasisChunk004.row4799_mem, Shared.BasisChunk004.row4800_mem, Shared.BasisChunk004.row4801_mem, Shared.BasisChunk004.row4802_mem, Shared.BasisChunk004.row4803_mem, Shared.BasisChunk004.row4804_mem, Shared.BasisChunk004.row4805_mem, Shared.BasisChunk004.row4806_mem, Shared.BasisChunk004.row4807_mem, Shared.BasisChunk004.row4809_mem, Shared.BasisChunk004.row4810_mem, Shared.BasisChunk004.row4811_mem, Shared.BasisChunk004.row4812_mem, Shared.BasisChunk004.row4814_mem, Shared.BasisChunk004.row4815_mem, Shared.BasisChunk004.row4817_mem, Shared.BasisChunk004.row4819_mem, Shared.BasisChunk004.row4820_mem, Shared.BasisChunk004.row4821_mem, Shared.BasisChunk004.row4822_mem, Shared.BasisChunk004.row4823_mem, Shared.BasisChunk004.row4824_mem, Shared.BasisChunk004.row4825_mem, Shared.BasisChunk004.row4826_mem, Shared.BasisChunk004.row4827_mem, Shared.BasisChunk004.row4828_mem, Shared.BasisChunk004.row4829_mem, Shared.BasisChunk004.row4830_mem, Shared.BasisChunk004.row4831_mem, Shared.BasisChunk004.row4833_mem, Shared.BasisChunk004.row4834_mem, Shared.BasisChunk004.row4835_mem, Shared.BasisChunk004.row4836_mem, Shared.BasisChunk004.row4837_mem, Shared.BasisChunk004.row4838_mem, Shared.BasisChunk004.row4840_mem, Shared.BasisChunk004.row4841_mem, Shared.BasisChunk004.row4842_mem, Shared.BasisChunk004.row4843_mem, Shared.BasisChunk004.row4844_mem, Shared.BasisChunk004.row4845_mem, Shared.BasisChunk004.row4846_mem, Shared.BasisChunk004.row4847_mem, Shared.BasisChunk004.row4848_mem, Shared.BasisChunk004.row4849_mem, Shared.BasisChunk004.row4850_mem, Shared.BasisChunk004.row4851_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard062
