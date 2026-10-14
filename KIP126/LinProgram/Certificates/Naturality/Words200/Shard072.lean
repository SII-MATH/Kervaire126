module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard072
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard072
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard072
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation57_zero, Shared.RelationChunk000.relation58_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation76_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation91_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk002.relation244_zero, Shared.RelationChunk003.relation253_zero, Shared.RelationChunk003.relation259_zero, Shared.RelationChunk005.relation357_zero, Shared.RelationChunk007.relation441_zero, Shared.RelationChunk008.relation446_zero, Shared.RelationChunk008.relation448_zero, Shared.RelationChunk008.relation463_zero, Shared.RelationChunk011.relation599_zero, Shared.RelationChunk011.relation600_zero, Shared.RelationChunk011.relation601_zero, Shared.RelationChunk011.relation602_zero, Shared.RelationChunk011.relation607_zero, Shared.RelationChunk011.relation608_zero, Shared.RelationChunk011.relation611_zero, Shared.RelationChunk013.relation667_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk014.relation709_zero, Shared.RelationChunk014.relation711_zero, Shared.RelationChunk014.relation712_zero, Shared.RelationChunk014.relation714_zero, Shared.RelationChunk014.relation716_zero, Shared.RelationChunk014.relation719_zero, Shared.RelationChunk014.relation720_zero, Shared.RelationChunk014.relation721_zero, Shared.RelationChunk014.relation723_zero, Shared.RelationChunk014.relation724_zero, Shared.RelationChunk014.relation725_zero, Shared.RelationChunk021.relation943_zero, Shared.RelationChunk021.relation944_zero, Shared.RelationChunk021.relation945_zero, Shared.RelationChunk022.relation984_zero, Shared.RelationChunk023.relation1007_zero, Shared.RelationChunk023.relation1008_zero, Shared.RelationChunk023.relation1009_zero, Shared.RelationChunk023.relation1010_zero, Shared.RelationChunk023.relation1011_zero, Shared.RelationChunk023.relation1012_zero, Shared.RelationChunk023.relation1013_zero, Shared.RelationChunk024.relation1037_zero, Shared.RelationChunk024.relation1039_zero, Shared.RelationChunk024.relation1040_zero, Shared.RelationChunk024.relation1041_zero, Shared.RelationChunk024.relation1042_zero, Shared.RelationChunk024.relation1043_zero, Shared.RelationChunk024.relation1044_zero, Shared.RelationChunk024.relation1049_zero, Shared.RelationChunk024.relation1050_zero, Shared.RelationChunk024.relation1051_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9218 128 := by cbv
private def targetRows : List BasisRow := [⟨9, 166, 0, "2,1,676,1"⟩,
  ⟨9, 166, 1, "1,1,697,1"⟩,
  ⟨9, 166, 2, "0,2,698,1"⟩,
  ⟨9, 166, 3, "0,2,23,1,324,1"⟩,
  ⟨8, 166, 1, "7,2,398,1"⟩,
  ⟨8, 166, 2, "1,1,18,1,368,1"⟩,
  ⟨8, 166, 3, "0,2,699,1"⟩,
  ⟨8, 166, 4, "0,6,18,1,324,1"⟩,
  ⟨7, 166, 1, "7,2,400,1"⟩,
  ⟨7, 166, 2, "0,1,18,1,378,1"⟩,
  ⟨7, 166, 3, "0,1,2,1,660,1"⟩,
  ⟨6, 166, 0, "2,1,18,1,341,1"⟩,
  ⟨6, 166, 1, "0,1,26,1,324,1"⟩,
  ⟨5, 166, 0, "0,2,2,1,18,1,324,1"⟩,
  ⟨167, 167, 0, "0,167"⟩,
  ⟨56, 167, 0, "0,11,606,1"⟩,
  ⟨54, 167, 0, "0,2,700,1"⟩,
  ⟨53, 167, 0, "0,2,701,1"⟩,
  ⟨50, 167, 0, "0,8,635,1"⟩,
  ⟨49, 167, 0, "0,8,636,1"⟩,
  ⟨44, 167, 0, "0,2,16,1,402,1"⟩,
  ⟨43, 167, 0, "0,2,16,1,403,1"⟩,
  ⟨43, 167, 1, "0,3,685,1"⟩,
  ⟨42, 167, 0, "0,2,17,1,403,1"⟩,
  ⟨41, 167, 0, "0,3,686,1"⟩,
  ⟨40, 167, 1, "0,39,324,1"⟩,
  ⟨39, 167, 0, "0,2,8,3,225,1"⟩,
  ⟨38, 167, 0, "723,1"⟩,
  ⟨37, 167, 0, "724,1"⟩,
  ⟨36, 167, 0, "8,2,343,1"⟩,
  ⟨35, 167, 0, "8,1,17,1,257,1"⟩,
  ⟨34, 167, 1, "8,2,344,1"⟩,
  ⟨33, 167, 0, "8,2,345,1"⟩,
  ⟨33, 167, 1, "0,2,64,1,185,1"⟩,
  ⟨32, 167, 0, "8,4,160,1"⟩,
  ⟨31, 167, 0, "8,3,232,1"⟩,
  ⟨30, 167, 1, "8,3,233,1"⟩,
  ⟨29, 167, 0, "8,1,17,1,260,1"⟩,
  ⟨29, 167, 1, "8,2,9,1,219,1"⟩,
  ⟨28, 167, 0, "726,1"⟩,
  ⟨28, 167, 1, "8,1,9,1,13,1,194,1"⟩,
  ⟨27, 167, 1, "9,1,13,2,167,1"⟩,
  ⟨27, 167, 2, "8,1,549,1"⟩,
  ⟨26, 167, 0, "8,2,347,1"⟩,
  ⟨26, 167, 1, "8,2,346,1"⟩,
  ⟨25, 167, 0, "8,1,550,1"⟩,
  ⟨25, 167, 1, "8,1,13,1,292,1"⟩,
  ⟨24, 167, 1, "23,1,346,1"⟩,
  ⟨24, 167, 2, "8,2,348,1"⟩,
  ⟨24, 167, 3, "0,2,64,1,187,1"⟩,
  ⟨23, 167, 0, "8,2,350,1"⟩,
  ⟨23, 167, 2, "0,1,69,1,185,1"⟩,
  ⟨23, 167, 3, "0,2,702,1"⟩,
  ⟨23, 167, 4, "0,2,64,1,188,1"⟩,
  ⟨22, 167, 0, "8,2,13,1,209,1"⟩,
  ⟨22, 167, 1, "0,1,3,1,627,1"⟩,
  ⟨22, 167, 2, "0,2,703,1"⟩,
  ⟨21, 167, 0, "8,1,13,1,294,1"⟩,
  ⟨21, 167, 1, "0,1,717,1"⟩,
  ⟨21, 167, 2, "0,2,706,1"⟩,
  ⟨20, 167, 1, "13,2,261,1"⟩,
  ⟨20, 167, 2, "0,1,3,1,628,1"⟩,
  ⟨20, 167, 3, "0,3,693,1"⟩,
  ⟨19, 167, 0, "13,2,262,1"⟩,
  ⟨19, 167, 2, "0,2,8,2,333,1"⟩,
  ⟨19, 167, 3, "0,5,671,1"⟩,
  ⟨18, 167, 1, "0,2,707,1"⟩,
  ⟨18, 167, 2, "0,2,8,1,534,1"⟩,
  ⟨17, 167, 0, "0,1,3,1,630,1"⟩,
  ⟨16, 167, 1, "0,1,67,1,190,1"⟩,
  ⟨15, 167, 0, "0,1,67,1,191,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5514_mem, Shared.BasisChunk005.row5515_mem, Shared.BasisChunk005.row5516_mem, Shared.BasisChunk005.row5517_mem, Shared.BasisChunk005.row5519_mem, Shared.BasisChunk005.row5520_mem, Shared.BasisChunk005.row5521_mem, Shared.BasisChunk005.row5522_mem, Shared.BasisChunk005.row5524_mem, Shared.BasisChunk005.row5525_mem, Shared.BasisChunk005.row5526_mem, Shared.BasisChunk005.row5527_mem, Shared.BasisChunk005.row5528_mem, Shared.BasisChunk005.row5529_mem, Shared.BasisChunk005.row5530_mem, Shared.BasisChunk005.row5531_mem, Shared.BasisChunk005.row5533_mem, Shared.BasisChunk005.row5534_mem, Shared.BasisChunk005.row5535_mem, Shared.BasisChunk005.row5536_mem, Shared.BasisChunk005.row5537_mem, Shared.BasisChunk005.row5538_mem, Shared.BasisChunk005.row5539_mem, Shared.BasisChunk005.row5540_mem, Shared.BasisChunk005.row5541_mem, Shared.BasisChunk005.row5543_mem, Shared.BasisChunk005.row5544_mem, Shared.BasisChunk005.row5545_mem, Shared.BasisChunk005.row5546_mem, Shared.BasisChunk005.row5547_mem, Shared.BasisChunk005.row5548_mem, Shared.BasisChunk005.row5550_mem, Shared.BasisChunk005.row5551_mem, Shared.BasisChunk005.row5552_mem, Shared.BasisChunk005.row5553_mem, Shared.BasisChunk005.row5554_mem, Shared.BasisChunk005.row5556_mem, Shared.BasisChunk005.row5557_mem, Shared.BasisChunk005.row5558_mem, Shared.BasisChunk005.row5559_mem, Shared.BasisChunk005.row5560_mem, Shared.BasisChunk005.row5562_mem, Shared.BasisChunk005.row5563_mem, Shared.BasisChunk005.row5564_mem, Shared.BasisChunk005.row5565_mem, Shared.BasisChunk005.row5566_mem, Shared.BasisChunk005.row5567_mem, Shared.BasisChunk005.row5569_mem, Shared.BasisChunk005.row5570_mem, Shared.BasisChunk005.row5571_mem, Shared.BasisChunk005.row5572_mem, Shared.BasisChunk005.row5574_mem, Shared.BasisChunk005.row5575_mem, Shared.BasisChunk005.row5576_mem, Shared.BasisChunk005.row5577_mem, Shared.BasisChunk005.row5578_mem, Shared.BasisChunk005.row5579_mem, Shared.BasisChunk005.row5580_mem, Shared.BasisChunk005.row5581_mem, Shared.BasisChunk005.row5582_mem, Shared.BasisChunk005.row5584_mem, Shared.BasisChunk005.row5585_mem, Shared.BasisChunk005.row5586_mem, Shared.BasisChunk005.row5587_mem, Shared.BasisChunk005.row5589_mem, Shared.BasisChunk005.row5590_mem, Shared.BasisChunk005.row5592_mem, Shared.BasisChunk005.row5593_mem, Shared.BasisChunk005.row5594_mem, Shared.BasisChunk005.row5596_mem, Shared.BasisChunk005.row5597_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard072
