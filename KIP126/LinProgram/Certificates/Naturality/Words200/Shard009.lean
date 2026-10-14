module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard009
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard009
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
  exact ⟨Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk001.relation152_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk001.relation159_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 1154 128 := by cbv
private def targetRows : List BasisRow := [⟨21, 79, 0, "0,1,8,2,31,1"⟩,
  ⟨20, 79, 0, "0,1,8,1,16,1,17,1"⟩,
  ⟨17, 79, 0, "0,7,90,1"⟩,
  ⟨16, 79, 1, "0,15,69,1"⟩,
  ⟨15, 79, 0, "0,1,112,1"⟩,
  ⟨14, 79, 0, "0,1,113,1"⟩,
  ⟨12, 79, 0, "0,3,106,1"⟩,
  ⟨11, 79, 0, "2,1,101,1"⟩,
  ⟨11, 79, 1, "0,3,107,1"⟩,
  ⟨10, 79, 0, "115,1"⟩,
  ⟨9, 79, 0, "1,1,108,1"⟩,
  ⟨80, 80, 0, "0,80"⟩,
  ⟨26, 80, 0, "0,2,110,1"⟩,
  ⟨25, 80, 1, "0,2,111,1"⟩,
  ⟨22, 80, 0, "0,2,8,2,31,1"⟩,
  ⟨21, 80, 0, "0,2,8,1,16,1,17,1"⟩,
  ⟨18, 80, 0, "0,8,90,1"⟩,
  ⟨17, 80, 0, "0,16,69,1"⟩,
  ⟨16, 80, 0, "0,2,112,1"⟩,
  ⟨15, 80, 0, "0,2,113,1"⟩,
  ⟨12, 80, 0, "0,1,2,1,101,1"⟩,
  ⟨12, 80, 1, "0,4,107,1"⟩,
  ⟨11, 80, 0, "2,1,103,1"⟩,
  ⟨11, 80, 1, "0,1,115,1"⟩,
  ⟨10, 80, 0, "1,2,107,1"⟩,
  ⟨9, 80, 0, "2,1,107,1"⟩,
  ⟨8, 80, 1, "3,2,68,1"⟩,
  ⟨7, 80, 0, "7,1,68,1"⟩,
  ⟨7, 80, 1, "2,2,92,1"⟩,
  ⟨6, 80, 0, "6,1,69,1"⟩,
  ⟨6, 80, 1, "3,1,93,1"⟩,
  ⟨5, 80, 0, "3,1,94,1"⟩,
  ⟨3, 80, 0, "3,2,69,1"⟩,
  ⟨81, 81, 0, "0,81"⟩,
  ⟨26, 81, 0, "0,3,111,1"⟩,
  ⟨23, 81, 0, "117,1"⟩,
  ⟨19, 81, 0, "8,2,40,1"⟩,
  ⟨19, 81, 1, "0,9,90,1"⟩,
  ⟨18, 81, 0, "8,1,17,1,20,1"⟩,
  ⟨18, 81, 1, "0,17,69,1"⟩,
  ⟨17, 81, 0, "8,1,63,1"⟩,
  ⟨17, 81, 1, "0,3,112,1"⟩,
  ⟨16, 81, 0, "8,2,9,1,13,1"⟩,
  ⟨15, 81, 0, "8,1,9,1,32,1"⟩,
  ⟨14, 81, 0, "9,1,13,1,23,1"⟩,
  ⟨13, 81, 0, "118,1"⟩,
  ⟨13, 81, 1, "0,5,107,1"⟩,
  ⟨10, 81, 0, "0,1,2,1,107,1"⟩,
  ⟨9, 81, 0, "0,1,3,2,68,1"⟩,
  ⟨8, 81, 0, "0,1,7,1,68,1"⟩,
  ⟨7, 81, 0, "0,1,6,1,69,1"⟩,
  ⟨6, 81, 0, "0,1,3,1,94,1"⟩,
  ⟨4, 81, 0, "0,1,3,2,69,1"⟩,
  ⟨3, 81, 0, "0,1,7,1,69,1"⟩,
  ⟨82, 82, 0, "0,82"⟩,
  ⟨27, 82, 0, "0,4,111,1"⟩,
  ⟨25, 82, 0, "0,1,116,1"⟩,
  ⟨24, 82, 0, "0,1,117,1"⟩,
  ⟨20, 82, 0, "0,10,90,1"⟩,
  ⟨19, 82, 0, "0,18,69,1"⟩,
  ⟨15, 82, 0, "0,1,8,1,64,1"⟩,
  ⟨14, 82, 0, "0,1,118,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row696_mem, Shared.BasisChunk000.row697_mem, Shared.BasisChunk000.row698_mem, Shared.BasisChunk000.row700_mem, Shared.BasisChunk000.row701_mem, Shared.BasisChunk000.row702_mem, Shared.BasisChunk000.row703_mem, Shared.BasisChunk000.row704_mem, Shared.BasisChunk000.row705_mem, Shared.BasisChunk000.row706_mem, Shared.BasisChunk000.row707_mem, Shared.BasisChunk000.row708_mem, Shared.BasisChunk000.row709_mem, Shared.BasisChunk000.row711_mem, Shared.BasisChunk000.row712_mem, Shared.BasisChunk000.row713_mem, Shared.BasisChunk000.row714_mem, Shared.BasisChunk000.row715_mem, Shared.BasisChunk000.row716_mem, Shared.BasisChunk000.row717_mem, Shared.BasisChunk000.row718_mem, Shared.BasisChunk000.row719_mem, Shared.BasisChunk000.row720_mem, Shared.BasisChunk000.row721_mem, Shared.BasisChunk000.row722_mem, Shared.BasisChunk000.row723_mem, Shared.BasisChunk000.row725_mem, Shared.BasisChunk000.row726_mem, Shared.BasisChunk000.row727_mem, Shared.BasisChunk000.row729_mem, Shared.BasisChunk000.row730_mem, Shared.BasisChunk000.row731_mem, Shared.BasisChunk000.row732_mem, Shared.BasisChunk000.row734_mem, Shared.BasisChunk000.row735_mem, Shared.BasisChunk000.row737_mem, Shared.BasisChunk000.row739_mem, Shared.BasisChunk000.row740_mem, Shared.BasisChunk000.row741_mem, Shared.BasisChunk000.row742_mem, Shared.BasisChunk000.row743_mem, Shared.BasisChunk000.row744_mem, Shared.BasisChunk000.row745_mem, Shared.BasisChunk000.row746_mem, Shared.BasisChunk000.row747_mem, Shared.BasisChunk000.row749_mem, Shared.BasisChunk000.row750_mem, Shared.BasisChunk000.row751_mem, Shared.BasisChunk000.row752_mem, Shared.BasisChunk000.row753_mem, Shared.BasisChunk000.row754_mem, Shared.BasisChunk000.row755_mem, Shared.BasisChunk000.row757_mem, Shared.BasisChunk000.row758_mem, Shared.BasisChunk000.row759_mem, Shared.BasisChunk000.row760_mem, Shared.BasisChunk000.row762_mem, Shared.BasisChunk000.row763_mem, Shared.BasisChunk000.row764_mem, Shared.BasisChunk000.row765_mem, Shared.BasisChunk000.row766_mem, Shared.BasisChunk000.row767_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard009
