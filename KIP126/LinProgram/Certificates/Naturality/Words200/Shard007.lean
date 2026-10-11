module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard007
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard007
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
  exact ⟨Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk000.relation127_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 898 128 := by cbv
private def targetRows : List BasisRow := [⟨72, 72, 0, "0,72"⟩,
  ⟨23, 72, 0, "0,3,77,1"⟩,
  ⟨19, 72, 0, "8,1,50,1"⟩,
  ⟨16, 72, 0, "8,4"⟩,
  ⟨15, 72, 0, "8,2,22,1"⟩,
  ⟨14, 72, 0, "8,2,23,1"⟩,
  ⟨13, 72, 0, "8,1,51,1"⟩,
  ⟨12, 72, 0, "13,3"⟩,
  ⟨12, 72, 1, "0,3,80,1"⟩,
  ⟨11, 72, 0, "23,1,24,1"⟩,
  ⟨11, 72, 1, "0,2,81,1"⟩,
  ⟨10, 72, 0, "90,1"⟩,
  ⟨10, 72, 1, "89,1"⟩,
  ⟨9, 72, 1, "0,2,84,1"⟩,
  ⟨9, 72, 2, "0,8,69,1"⟩,
  ⟨8, 72, 1, "0,1,2,1,75,1"⟩,
  ⟨8, 72, 2, "0,2,86,1"⟩,
  ⟨7, 72, 0, "3,1,68,1"⟩,
  ⟨7, 72, 1, "2,1,18,1,24,1"⟩,
  ⟨6, 72, 0, "91,1"⟩,
  ⟨5, 72, 0, "93,1"⟩,
  ⟨4, 72, 0, "94,1"⟩,
  ⟨3, 72, 0, "2,2,69,1"⟩,
  ⟨73, 73, 0, "0,73"⟩,
  ⟨24, 73, 0, "1,1,87,1"⟩,
  ⟨21, 73, 0, "0,1,8,1,49,1"⟩,
  ⟨20, 73, 0, "0,1,8,1,50,1"⟩,
  ⟨13, 73, 0, "0,4,80,1"⟩,
  ⟨12, 73, 0, "0,3,81,1"⟩,
  ⟨11, 73, 0, "0,1,90,1"⟩,
  ⟨11, 73, 1, "0,1,89,1"⟩,
  ⟨10, 73, 0, "2,1,80,1"⟩,
  ⟨10, 73, 1, "0,9,69,1"⟩,
  ⟨9, 73, 0, "0,1,3,1,67,1"⟩,
  ⟨8, 73, 0, "0,1,3,1,68,1"⟩,
  ⟨7, 73, 1, "0,1,91,1"⟩,
  ⟨6, 73, 0, "0,1,93,1"⟩,
  ⟨6, 73, 1, "0,1,92,1"⟩,
  ⟨5, 73, 0, "0,1,94,1"⟩,
  ⟨3, 73, 0, "0,1,3,1,69,1"⟩,
  ⟨74, 74, 0, "0,74"⟩,
  ⟨22, 74, 0, "0,2,8,1,49,1"⟩,
  ⟨21, 74, 0, "0,2,8,1,50,1"⟩,
  ⟨14, 74, 0, "0,5,80,1"⟩,
  ⟨13, 74, 0, "0,4,81,1"⟩,
  ⟨12, 74, 0, "0,2,90,1"⟩,
  ⟨12, 74, 1, "0,2,89,1"⟩,
  ⟨11, 74, 0, "1,2,81,1"⟩,
  ⟨11, 74, 1, "0,1,2,1,80,1"⟩,
  ⟨11, 74, 2, "0,10,69,1"⟩,
  ⟨10, 74, 1, "0,2,3,1,67,1"⟩,
  ⟨9, 74, 0, "2,1,82,1"⟩,
  ⟨9, 74, 1, "0,2,3,1,68,1"⟩,
  ⟨8, 74, 0, "0,1,95,1"⟩,
  ⟨7, 74, 0, "0,2,92,1"⟩,
  ⟨5, 74, 0, "0,1,96,1"⟩,
  ⟨4, 74, 1, "0,2,3,1,69,1"⟩,
  ⟨75, 75, 0, "0,75"⟩,
  ⟨19, 75, 0, "8,1,56,1"⟩,
  ⟨18, 75, 0, "17,1,40,1"⟩,
  ⟨17, 75, 0, "100,1"⟩,
  ⟨16, 75, 0, "8,3,9,1"⟩,
  ⟨15, 75, 0, "8,2,29,1"⟩,
  ⟨14, 75, 0, "8,1,9,1,23,1"⟩,
  ⟨13, 75, 0, "9,1,51,1"⟩,
  ⟨13, 75, 1, "0,3,90,1"⟩,
  ⟨12, 75, 0, "0,11,69,1"⟩,
  ⟨8, 75, 0, "1,1,95,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row534_mem, Shared.BasisChunk000.row535_mem, Shared.BasisChunk000.row537_mem, Shared.BasisChunk000.row539_mem, Shared.BasisChunk000.row540_mem, Shared.BasisChunk000.row541_mem, Shared.BasisChunk000.row542_mem, Shared.BasisChunk000.row543_mem, Shared.BasisChunk000.row544_mem, Shared.BasisChunk000.row545_mem, Shared.BasisChunk000.row546_mem, Shared.BasisChunk000.row547_mem, Shared.BasisChunk000.row548_mem, Shared.BasisChunk000.row551_mem, Shared.BasisChunk000.row552_mem, Shared.BasisChunk000.row554_mem, Shared.BasisChunk000.row555_mem, Shared.BasisChunk000.row556_mem, Shared.BasisChunk000.row557_mem, Shared.BasisChunk000.row558_mem, Shared.BasisChunk000.row559_mem, Shared.BasisChunk000.row561_mem, Shared.BasisChunk000.row562_mem, Shared.BasisChunk000.row564_mem, Shared.BasisChunk000.row565_mem, Shared.BasisChunk000.row566_mem, Shared.BasisChunk000.row567_mem, Shared.BasisChunk000.row568_mem, Shared.BasisChunk000.row569_mem, Shared.BasisChunk000.row570_mem, Shared.BasisChunk000.row571_mem, Shared.BasisChunk000.row572_mem, Shared.BasisChunk000.row573_mem, Shared.BasisChunk000.row574_mem, Shared.BasisChunk000.row575_mem, Shared.BasisChunk000.row577_mem, Shared.BasisChunk000.row578_mem, Shared.BasisChunk000.row579_mem, Shared.BasisChunk000.row580_mem, Shared.BasisChunk000.row582_mem, Shared.BasisChunk000.row583_mem, Shared.BasisChunk000.row585_mem, Shared.BasisChunk000.row586_mem, Shared.BasisChunk000.row588_mem, Shared.BasisChunk000.row589_mem, Shared.BasisChunk000.row590_mem, Shared.BasisChunk000.row591_mem, Shared.BasisChunk000.row592_mem, Shared.BasisChunk000.row593_mem, Shared.BasisChunk000.row594_mem, Shared.BasisChunk000.row596_mem, Shared.BasisChunk000.row597_mem, Shared.BasisChunk000.row598_mem, Shared.BasisChunk000.row599_mem, Shared.BasisChunk000.row600_mem, Shared.BasisChunk000.row602_mem, Shared.BasisChunk000.row604_mem, Shared.BasisChunk000.row606_mem, Shared.BasisChunk000.row608_mem, Shared.BasisChunk000.row609_mem, Shared.BasisChunk000.row610_mem, Shared.BasisChunk000.row611_mem, Shared.BasisChunk000.row612_mem, Shared.BasisChunk000.row613_mem, Shared.BasisChunk000.row614_mem, Shared.BasisChunk000.row615_mem, Shared.BasisChunk000.row616_mem, Shared.BasisChunk000.row618_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard007
