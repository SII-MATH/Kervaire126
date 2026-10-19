module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard055
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard055
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard055
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation4_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation36_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation80_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation93_zero, Shared.RelationChunk000.relation94_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation154_zero, Shared.RelationChunk001.relation155_zero, Shared.RelationChunk001.relation157_zero, Shared.RelationChunk001.relation158_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation234_zero, Shared.RelationChunk002.relation235_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk005.relation325_zero, Shared.RelationChunk005.relation326_zero, Shared.RelationChunk005.relation327_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk005.relation331_zero, Shared.RelationChunk005.relation332_zero, Shared.RelationChunk005.relation333_zero, Shared.RelationChunk006.relation364_zero, Shared.RelationChunk007.relation419_zero, Shared.RelationChunk009.relation489_zero, Shared.RelationChunk014.relation751_zero, Shared.RelationChunk015.relation756_zero, Shared.RelationChunk015.relation777_zero, Shared.RelationChunk015.relation786_zero, Shared.RelationChunk016.relation791_zero, Shared.RelationChunk016.relation793_zero, Shared.RelationChunk016.relation794_zero, Shared.RelationChunk016.relation795_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7042 128 := by cbv
private def targetRows : List BasisRow := [⟨37, 153, 1, "8,3,171,1"⟩,
  ⟨36, 153, 0, "8,6,39,1"⟩,
  ⟨35, 153, 0, "8,6,40,1"⟩,
  ⟨34, 153, 1, "8,5,17,1,20,1"⟩,
  ⟨33, 153, 0, "8,2,16,1,138,1"⟩,
  ⟨33, 153, 1, "8,5,63,1"⟩,
  ⟨32, 153, 0, "8,2,17,1,138,1"⟩,
  ⟨32, 153, 1, "8,6,9,1,13,1"⟩,
  ⟨31, 153, 0, "8,1,42,1,137,1"⟩,
  ⟨31, 153, 1, "8,5,9,1,32,1"⟩,
  ⟨31, 153, 2, "0,3,64,1,137,1"⟩,
  ⟨30, 153, 0, "8,4,9,1,13,1,23,1"⟩,
  ⟨30, 153, 1, "8,5,64,1"⟩,
  ⟨30, 153, 2, "0,3,64,1,138,1"⟩,
  ⟨29, 153, 0, "8,3,9,1,13,1,51,1"⟩,
  ⟨29, 153, 1, "8,4,118,1"⟩,
  ⟨29, 153, 2, "0,4,17,1,260,1"⟩,
  ⟨28, 153, 1, "8,2,9,1,13,4"⟩,
  ⟨28, 153, 2, "8,3,17,1,80,1"⟩,
  ⟨28, 153, 3, "0,3,558,1"⟩,
  ⟨27, 153, 0, "64,1,147,1"⟩,
  ⟨27, 153, 1, "8,1,9,1,13,3,32,1"⟩,
  ⟨27, 153, 2, "8,3,173,1"⟩,
  ⟨27, 153, 3, "0,1,8,1,380,1"⟩,
  ⟨27, 153, 4, "0,9,500,1"⟩,
  ⟨26, 153, 0, "9,1,13,4,23,1"⟩,
  ⟨26, 153, 1, "8,1,404,1"⟩,
  ⟨26, 153, 2, "8,3,13,1,101,1"⟩,
  ⟨26, 153, 3, "0,1,17,1,278,1"⟩,
  ⟨26, 153, 4, "0,25,324,1"⟩,
  ⟨25, 153, 0, "580,1"⟩,
  ⟨25, 153, 1, "8,2,13,2,80,1"⟩,
  ⟨25, 153, 2, "0,1,573,1"⟩,
  ⟨24, 153, 0, "8,1,13,1,23,1,101,1"⟩,
  ⟨24, 153, 1, "8,2,254,1"⟩,
  ⟨23, 153, 0, "13,2,23,1,80,1"⟩,
  ⟨23, 153, 1, "8,2,255,1"⟩,
  ⟨22, 153, 0, "8,1,20,1,188,1"⟩,
  ⟨21, 153, 0, "20,1,267,1"⟩,
  ⟨21, 153, 1, "0,2,18,1,260,1"⟩,
  ⟨20, 153, 0, "9,1,13,1,212,1"⟩,
  ⟨20, 153, 2, "0,2,69,1,138,1"⟩,
  ⟨19, 153, 0, "13,1,328,1"⟩,
  ⟨19, 153, 1, "0,2,568,1"⟩,
  ⟨18, 153, 0, "581,1"⟩,
  ⟨17, 153, 1, "0,1,7,2,267,1"⟩,
  ⟨16, 153, 0, "0,2,8,1,69,1,80,1"⟩,
  ⟨15, 153, 0, "13,1,331,1"⟩,
  ⟨14, 153, 0, "13,1,332,1"⟩,
  ⟨14, 153, 2, "3,2,425,1"⟩,
  ⟨14, 153, 3, "0,3,562,1"⟩,
  ⟨13, 153, 1, "7,1,425,1"⟩,
  ⟨13, 153, 2, "0,1,575,1"⟩,
  ⟨13, 153, 3, "0,5,546,1"⟩,
  ⟨12, 153, 0, "8,1,415,1"⟩,
  ⟨12, 153, 1, "1,1,7,1,412,1"⟩,
  ⟨12, 153, 2, "0,1,2,1,544,1"⟩,
  ⟨12, 153, 3, "0,2,7,1,414,1"⟩,
  ⟨11, 153, 0, "583,1"⟩,
  ⟨11, 153, 2, "0,1,3,1,504,1"⟩,
  ⟨11, 153, 3, "0,2,7,1,415,1"⟩,
  ⟨10, 153, 0, "2,1,69,1,134,1"⟩,
  ⟨10, 153, 1, "1,1,12,1,69,2"⟩,
  ⟨9, 153, 0, "1,1,12,1,324,1"⟩,
  ⟨9, 153, 1, "0,1,577,1"⟩,
  ⟨8, 153, 0, "7,1,430,1"⟩,
  ⟨7, 153, 0, "584,1"⟩,
  ⟨7, 153, 1, "0,1,3,1,506,1"⟩,
  ⟨6, 153, 0, "0,1,13,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4245_mem, Shared.BasisChunk004.row4246_mem, Shared.BasisChunk004.row4247_mem, Shared.BasisChunk004.row4249_mem, Shared.BasisChunk004.row4250_mem, Shared.BasisChunk004.row4251_mem, Shared.BasisChunk004.row4252_mem, Shared.BasisChunk004.row4253_mem, Shared.BasisChunk004.row4254_mem, Shared.BasisChunk004.row4255_mem, Shared.BasisChunk004.row4256_mem, Shared.BasisChunk004.row4257_mem, Shared.BasisChunk004.row4258_mem, Shared.BasisChunk004.row4259_mem, Shared.BasisChunk004.row4260_mem, Shared.BasisChunk004.row4261_mem, Shared.BasisChunk004.row4262_mem, Shared.BasisChunk004.row4264_mem, Shared.BasisChunk004.row4265_mem, Shared.BasisChunk004.row4266_mem, Shared.BasisChunk004.row4267_mem, Shared.BasisChunk004.row4268_mem, Shared.BasisChunk004.row4269_mem, Shared.BasisChunk004.row4270_mem, Shared.BasisChunk004.row4271_mem, Shared.BasisChunk004.row4272_mem, Shared.BasisChunk004.row4273_mem, Shared.BasisChunk004.row4274_mem, Shared.BasisChunk004.row4275_mem, Shared.BasisChunk004.row4276_mem, Shared.BasisChunk004.row4277_mem, Shared.BasisChunk004.row4278_mem, Shared.BasisChunk004.row4279_mem, Shared.BasisChunk004.row4280_mem, Shared.BasisChunk004.row4281_mem, Shared.BasisChunk004.row4282_mem, Shared.BasisChunk004.row4283_mem, Shared.BasisChunk004.row4284_mem, Shared.BasisChunk004.row4285_mem, Shared.BasisChunk004.row4286_mem, Shared.BasisChunk004.row4287_mem, Shared.BasisChunk004.row4289_mem, Shared.BasisChunk004.row4290_mem, Shared.BasisChunk004.row4291_mem, Shared.BasisChunk004.row4292_mem, Shared.BasisChunk004.row4294_mem, Shared.BasisChunk004.row4295_mem, Shared.BasisChunk004.row4296_mem, Shared.BasisChunk004.row4297_mem, Shared.BasisChunk004.row4299_mem, Shared.BasisChunk004.row4300_mem, Shared.BasisChunk004.row4302_mem, Shared.BasisChunk004.row4303_mem, Shared.BasisChunk004.row4304_mem, Shared.BasisChunk004.row4305_mem, Shared.BasisChunk004.row4306_mem, Shared.BasisChunk004.row4307_mem, Shared.BasisChunk004.row4308_mem, Shared.BasisChunk004.row4309_mem, Shared.BasisChunk004.row4311_mem, Shared.BasisChunk004.row4312_mem, Shared.BasisChunk004.row4313_mem, Shared.BasisChunk004.row4314_mem, Shared.BasisChunk004.row4316_mem, Shared.BasisChunk004.row4317_mem, Shared.BasisChunk004.row4318_mem, Shared.BasisChunk004.row4319_mem, Shared.BasisChunk004.row4320_mem, Shared.BasisChunk004.row4321_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard055
