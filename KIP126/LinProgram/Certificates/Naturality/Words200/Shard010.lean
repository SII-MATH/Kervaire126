module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard010
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard010
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation171_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1282 128 := by cbv
private def targetRows : List BasisRow := [⟨12, 82, 0, "2,1,114,1"⟩,
  ⟨10, 82, 0, "8,1,68,1"⟩,
  ⟨9, 82, 0, "0,2,7,1,68,1"⟩,
  ⟨8, 82, 1, "0,2,6,1,69,1"⟩,
  ⟨4, 82, 0, "0,2,7,1,69,1"⟩,
  ⟨83, 83, 0, "0,83"⟩,
  ⟨28, 83, 0, "0,5,111,1"⟩,
  ⟨26, 83, 0, "0,2,116,1"⟩,
  ⟨25, 83, 0, "0,2,117,1"⟩,
  ⟨21, 83, 0, "0,11,90,1"⟩,
  ⟨20, 83, 0, "0,19,69,1"⟩,
  ⟨16, 83, 0, "0,2,8,1,64,1"⟩,
  ⟨15, 83, 0, "0,2,118,1"⟩,
  ⟨12, 83, 1, "0,1,7,1,72,1"⟩,
  ⟨11, 83, 0, "0,1,8,1,68,1"⟩,
  ⟨9, 83, 0, "0,1,120,1"⟩,
  ⟨8, 83, 1, "0,1,121,1"⟩,
  ⟨7, 83, 0, "3,2,76,1"⟩,
  ⟨7, 83, 1, "0,1,122,1"⟩,
  ⟨6, 83, 0, "1,1,7,1,70,1"⟩,
  ⟨6, 83, 1, "0,1,8,1,69,1"⟩,
  ⟨5, 83, 0, "0,3,7,1,69,1"⟩,
  ⟨84, 84, 0, "0,84"⟩,
  ⟨27, 84, 0, "0,3,116,1"⟩,
  ⟨23, 84, 0, "16,1,50,1"⟩,
  ⟨22, 84, 0, "17,1,50,1"⟩,
  ⟨21, 84, 1, "0,20,69,1"⟩,
  ⟨20, 84, 0, "8,3,16,1"⟩,
  ⟨19, 84, 0, "8,3,17,1"⟩,
  ⟨18, 84, 0, "8,1,16,1,23,1"⟩,
  ⟨17, 84, 0, "8,2,42,1"⟩,
  ⟨16, 84, 0, "8,2,13,2"⟩,
  ⟨15, 84, 0, "8,1,13,1,32,1"⟩,
  ⟨14, 84, 0, "13,2,23,1"⟩,
  ⟨13, 84, 0, "127,1"⟩,
  ⟨13, 84, 1, "126,1"⟩,
  ⟨13, 84, 2, "13,2,24,1"⟩,
  ⟨12, 84, 0, "0,2,8,1,68,1"⟩,
  ⟨10, 84, 0, "0,2,120,1"⟩,
  ⟨9, 84, 1, "0,2,121,1"⟩,
  ⟨8, 84, 1, "0,2,122,1"⟩,
  ⟨7, 84, 1, "128,1"⟩,
  ⟨7, 84, 2, "1,1,122,1"⟩,
  ⟨7, 84, 3, "0,2,8,1,69,1"⟩,
  ⟨6, 84, 0, "130,1"⟩,
  ⟨6, 84, 2, "0,4,7,1,69,1"⟩,
  ⟨4, 84, 0, "132,1"⟩,
  ⟨3, 84, 0, "2,1,7,1,69,1"⟩,
  ⟨85, 85, 0, "0,85"⟩,
  ⟨28, 85, 0, "1,1,123,1"⟩,
  ⟨25, 85, 0, "0,1,8,1,71,1"⟩,
  ⟨24, 85, 0, "0,1,16,1,50,1"⟩,
  ⟨23, 85, 0, "0,1,17,1,50,1"⟩,
  ⟨22, 85, 0, "0,21,69,1"⟩,
  ⟨15, 85, 0, "0,1,8,1,72,1"⟩,
  ⟨14, 85, 0, "0,1,127,1"⟩,
  ⟨14, 85, 1, "0,1,126,1"⟩,
  ⟨13, 85, 0, "1,1,124,1"⟩,
  ⟨11, 85, 0, "0,3,120,1"⟩,
  ⟨10, 85, 0, "0,1,3,1,107,1"⟩,
  ⟨9, 85, 0, "133,1"⟩,
  ⟨9, 85, 1, "0,3,122,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row769_mem, Shared.BasisChunk000.row771_mem, Shared.BasisChunk000.row772_mem, Shared.BasisChunk000.row774_mem, Shared.BasisChunk000.row778_mem, Shared.BasisChunk000.row780_mem, Shared.BasisChunk000.row781_mem, Shared.BasisChunk000.row783_mem, Shared.BasisChunk000.row784_mem, Shared.BasisChunk000.row785_mem, Shared.BasisChunk000.row786_mem, Shared.BasisChunk000.row787_mem, Shared.BasisChunk000.row788_mem, Shared.BasisChunk000.row790_mem, Shared.BasisChunk000.row791_mem, Shared.BasisChunk000.row792_mem, Shared.BasisChunk000.row794_mem, Shared.BasisChunk000.row795_mem, Shared.BasisChunk000.row796_mem, Shared.BasisChunk000.row797_mem, Shared.BasisChunk000.row798_mem, Shared.BasisChunk000.row799_mem, Shared.BasisChunk000.row800_mem, Shared.BasisChunk000.row801_mem, Shared.BasisChunk000.row803_mem, Shared.BasisChunk000.row804_mem, Shared.BasisChunk000.row806_mem, Shared.BasisChunk000.row807_mem, Shared.BasisChunk000.row808_mem, Shared.BasisChunk000.row809_mem, Shared.BasisChunk000.row810_mem, Shared.BasisChunk000.row811_mem, Shared.BasisChunk000.row812_mem, Shared.BasisChunk000.row813_mem, Shared.BasisChunk000.row816_mem, Shared.BasisChunk000.row817_mem, Shared.BasisChunk000.row818_mem, Shared.BasisChunk000.row819_mem, Shared.BasisChunk000.row820_mem, Shared.BasisChunk000.row822_mem, Shared.BasisChunk000.row824_mem, Shared.BasisChunk000.row826_mem, Shared.BasisChunk000.row827_mem, Shared.BasisChunk000.row828_mem, Shared.BasisChunk000.row829_mem, Shared.BasisChunk000.row831_mem, Shared.BasisChunk000.row833_mem, Shared.BasisChunk000.row835_mem, Shared.BasisChunk000.row836_mem, Shared.BasisChunk000.row837_mem, Shared.BasisChunk000.row838_mem, Shared.BasisChunk000.row839_mem, Shared.BasisChunk000.row840_mem, Shared.BasisChunk000.row841_mem, Shared.BasisChunk000.row842_mem, Shared.BasisChunk000.row843_mem, Shared.BasisChunk000.row844_mem, Shared.BasisChunk000.row845_mem, Shared.BasisChunk000.row846_mem, Shared.BasisChunk000.row847_mem, Shared.BasisChunk000.row848_mem, Shared.BasisChunk000.row849_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard010
