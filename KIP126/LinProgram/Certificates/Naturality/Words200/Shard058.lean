module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard058
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard058
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard058
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation36_zero, Shared.RelationChunk000.relation42_zero, Shared.RelationChunk000.relation43_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation95_zero, Shared.RelationChunk000.relation96_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk000.relation106_zero, Shared.RelationChunk000.relation107_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation171_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk003.relation252_zero, Shared.RelationChunk003.relation255_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk004.relation322_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation348_zero, Shared.RelationChunk005.relation349_zero, Shared.RelationChunk005.relation350_zero, Shared.RelationChunk005.relation351_zero, Shared.RelationChunk005.relation352_zero, Shared.RelationChunk005.relation353_zero, Shared.RelationChunk005.relation356_zero, Shared.RelationChunk006.relation406_zero, Shared.RelationChunk009.relation518_zero, Shared.RelationChunk010.relation525_zero, Shared.RelationChunk010.relation526_zero, Shared.RelationChunk010.relation535_zero, Shared.RelationChunk010.relation537_zero, Shared.RelationChunk017.relation833_zero, Shared.RelationChunk017.relation835_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk017.relation837_zero, Shared.RelationChunk017.relation838_zero, Shared.RelationChunk017.relation839_zero, Shared.RelationChunk017.relation840_zero, Shared.RelationChunk017.relation841_zero, Shared.RelationChunk017.relation842_zero, Shared.RelationChunk017.relation843_zero, Shared.RelationChunk017.relation844_zero, Shared.RelationChunk017.relation846_zero, Shared.RelationChunk017.relation847_zero, Shared.RelationChunk017.relation848_zero, Shared.RelationChunk017.relation849_zero, Shared.RelationChunk017.relation850_zero, Shared.RelationChunk017.relation851_zero, Shared.RelationChunk017.relation852_zero, Shared.RelationChunk017.relation854_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7426 128 := by cbv
private def targetRows : List BasisRow := [⟨10, 155, 1, "3,1,535,1"⟩,
  ⟨10, 155, 2, "0,1,3,1,524,1"⟩,
  ⟨9, 155, 0, "2,1,18,1,264,1"⟩,
  ⟨9, 155, 1, "0,2,584,1"⟩,
  ⟨8, 155, 0, "0,1,7,1,446,1"⟩,
  ⟨156, 156, 0, "0,156"⟩,
  ⟨51, 156, 0, "0,3,578,1"⟩,
  ⟨47, 156, 0, "16,1,296,1"⟩,
  ⟨46, 156, 0, "17,1,296,1"⟩,
  ⟨45, 156, 0, "607,1"⟩,
  ⟨44, 156, 0, "8,3,182,1"⟩,
  ⟨43, 156, 0, "8,3,183,1"⟩,
  ⟨42, 156, 0, "8,1,16,1,17,1,111,1"⟩,
  ⟨41, 156, 0, "8,2,265,1"⟩,
  ⟨40, 156, 0, "8,5,71,1"⟩,
  ⟨39, 156, 0, "8,4,16,1,50,1"⟩,
  ⟨38, 156, 1, "8,4,17,1,50,1"⟩,
  ⟨37, 156, 0, "8,1,433,1"⟩,
  ⟨37, 156, 1, "8,4,125,1"⟩,
  ⟨37, 156, 2, "0,1,595,1"⟩,
  ⟨36, 156, 0, "17,1,298,1"⟩,
  ⟨36, 156, 1, "8,7,16,1"⟩,
  ⟨35, 156, 0, "8,7,17,1"⟩,
  ⟨35, 156, 1, "0,1,596,1"⟩,
  ⟨34, 156, 1, "8,5,16,1,23,1"⟩,
  ⟨34, 156, 2, "0,6,64,1,137,1"⟩,
  ⟨33, 156, 0, "8,3,185,1"⟩,
  ⟨33, 156, 1, "8,6,42,1"⟩,
  ⟨33, 156, 2, "0,6,64,1,138,1"⟩,
  ⟨32, 156, 0, "8,2,17,1,147,1"⟩,
  ⟨32, 156, 1, "8,6,13,2"⟩,
  ⟨31, 156, 0, "8,1,17,2,113,1"⟩,
  ⟨31, 156, 1, "8,5,13,1,32,1"⟩,
  ⟨31, 156, 2, "0,6,558,1"⟩,
  ⟨30, 156, 0, "8,4,13,2,23,1"⟩,
  ⟨30, 156, 1, "8,5,72,1"⟩,
  ⟨30, 156, 2, "0,12,500,1"⟩,
  ⟨29, 156, 0, "8,3,13,2,51,1"⟩,
  ⟨29, 156, 1, "8,4,127,1"⟩,
  ⟨29, 156, 2, "0,28,324,1"⟩,
  ⟨28, 156, 1, "8,2,13,5"⟩,
  ⟨28, 156, 2, "8,3,20,1,80,1"⟩,
  ⟨27, 156, 0, "16,1,299,1"⟩,
  ⟨27, 156, 1, "8,1,13,4,32,1"⟩,
  ⟨27, 156, 2, "8,3,186,1"⟩,
  ⟨27, 156, 3, "0,1,64,1,149,1"⟩,
  ⟨27, 156, 4, "0,1,8,2,260,1"⟩,
  ⟨26, 156, 0, "13,5,23,1"⟩,
  ⟨26, 156, 1, "8,1,434,1"⟩,
  ⟨26, 156, 2, "8,2,9,1,13,1,101,1"⟩,
  ⟨26, 156, 3, "0,1,598,1"⟩,
  ⟨26, 156, 4, "0,1,16,1,292,1"⟩,
  ⟨25, 156, 0, "13,5,24,1"⟩,
  ⟨25, 156, 1, "8,1,435,1"⟩,
  ⟨25, 156, 2, "8,1,9,1,13,2,80,1"⟩,
  ⟨25, 156, 3, "0,1,17,1,292,1"⟩,
  ⟨24, 156, 0, "9,1,13,1,23,1,101,1"⟩,
  ⟨24, 156, 1, "8,3,187,1"⟩,
  ⟨24, 156, 2, "0,1,601,1"⟩,
  ⟨24, 156, 3, "0,1,600,1"⟩,
  ⟨23, 156, 0, "8,3,188,1"⟩,
  ⟨23, 156, 1, "1,1,585,1"⟩,
  ⟨23, 156, 2, "0,2,586,1"⟩,
  ⟨22, 156, 0, "8,2,267,1"⟩,
  ⟨22, 156, 1, "2,2,538,1"⟩,
  ⟨21, 156, 0, "13,1,357,1"⟩,
  ⟨21, 156, 1, "8,1,23,1,188,1"⟩,
  ⟨21, 156, 3, "0,2,18,1,278,1"⟩,
  ⟨20, 156, 1, "13,1,359,1"⟩,
  ⟨20, 156, 2, "13,2,212,1"⟩,
  ⟨20, 156, 3, "0,2,69,1,147,1"⟩,
  ⟨20, 156, 4, "0,3,582,1"⟩,
  ⟨19, 156, 0, "609,1"⟩,
  ⟨19, 156, 1, "13,1,360,1"⟩,
  ⟨18, 156, 0, "611,1"⟩,
  ⟨18, 156, 1, "610,1"⟩,
  ⟨17, 156, 1, "13,2,213,1"⟩,
  ⟨17, 156, 2, "0,1,604,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4463_mem, Shared.BasisChunk004.row4464_mem, Shared.BasisChunk004.row4465_mem, Shared.BasisChunk004.row4466_mem, Shared.BasisChunk004.row4467_mem, Shared.BasisChunk004.row4470_mem, Shared.BasisChunk004.row4471_mem, Shared.BasisChunk004.row4473_mem, Shared.BasisChunk004.row4474_mem, Shared.BasisChunk004.row4475_mem, Shared.BasisChunk004.row4477_mem, Shared.BasisChunk004.row4478_mem, Shared.BasisChunk004.row4479_mem, Shared.BasisChunk004.row4480_mem, Shared.BasisChunk004.row4481_mem, Shared.BasisChunk004.row4482_mem, Shared.BasisChunk004.row4484_mem, Shared.BasisChunk004.row4486_mem, Shared.BasisChunk004.row4487_mem, Shared.BasisChunk004.row4488_mem, Shared.BasisChunk004.row4489_mem, Shared.BasisChunk004.row4490_mem, Shared.BasisChunk004.row4491_mem, Shared.BasisChunk004.row4492_mem, Shared.BasisChunk004.row4494_mem, Shared.BasisChunk004.row4495_mem, Shared.BasisChunk004.row4496_mem, Shared.BasisChunk004.row4497_mem, Shared.BasisChunk004.row4498_mem, Shared.BasisChunk004.row4499_mem, Shared.BasisChunk004.row4500_mem, Shared.BasisChunk004.row4501_mem, Shared.BasisChunk004.row4502_mem, Shared.BasisChunk004.row4503_mem, Shared.BasisChunk004.row4504_mem, Shared.BasisChunk004.row4505_mem, Shared.BasisChunk004.row4506_mem, Shared.BasisChunk004.row4507_mem, Shared.BasisChunk004.row4508_mem, Shared.BasisChunk004.row4509_mem, Shared.BasisChunk004.row4511_mem, Shared.BasisChunk004.row4512_mem, Shared.BasisChunk004.row4513_mem, Shared.BasisChunk004.row4514_mem, Shared.BasisChunk004.row4515_mem, Shared.BasisChunk004.row4516_mem, Shared.BasisChunk004.row4517_mem, Shared.BasisChunk004.row4518_mem, Shared.BasisChunk004.row4519_mem, Shared.BasisChunk004.row4520_mem, Shared.BasisChunk004.row4521_mem, Shared.BasisChunk004.row4522_mem, Shared.BasisChunk004.row4523_mem, Shared.BasisChunk004.row4524_mem, Shared.BasisChunk004.row4525_mem, Shared.BasisChunk004.row4526_mem, Shared.BasisChunk004.row4527_mem, Shared.BasisChunk004.row4528_mem, Shared.BasisChunk004.row4529_mem, Shared.BasisChunk004.row4530_mem, Shared.BasisChunk004.row4531_mem, Shared.BasisChunk004.row4532_mem, Shared.BasisChunk004.row4533_mem, Shared.BasisChunk004.row4534_mem, Shared.BasisChunk004.row4535_mem, Shared.BasisChunk004.row4537_mem, Shared.BasisChunk004.row4538_mem, Shared.BasisChunk004.row4540_mem, Shared.BasisChunk004.row4542_mem, Shared.BasisChunk004.row4543_mem, Shared.BasisChunk004.row4544_mem, Shared.BasisChunk004.row4545_mem, Shared.BasisChunk004.row4546_mem, Shared.BasisChunk004.row4547_mem, Shared.BasisChunk004.row4548_mem, Shared.BasisChunk004.row4549_mem, Shared.BasisChunk004.row4551_mem, Shared.BasisChunk004.row4552_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard058
