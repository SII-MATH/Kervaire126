module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard053
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard053
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard053
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
  exact ⟨Shared.RelationChunk003.relation256_zero, Shared.RelationChunk007.relation438_zero, Shared.RelationChunk014.relation704_zero, Shared.RelationChunk014.relation752_zero, Shared.RelationChunk014.relation753_zero, Shared.RelationChunk015.relation782_zero, Shared.RelationChunk015.relation783_zero, Shared.RelationChunk015.relation784_zero, Shared.RelationChunk015.relation785_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6786 128 := by cbv
private def targetRows : List BasisRow := [⟨29, 151, 0, "0,1,64,1,137,1"⟩,
  ⟨28, 151, 0, "0,1,64,1,138,1"⟩,
  ⟨28, 151, 1, "0,2,16,1,260,1"⟩,
  ⟨27, 151, 0, "0,1,557,1"⟩,
  ⟨27, 151, 1, "0,2,17,1,260,1"⟩,
  ⟨26, 151, 0, "0,1,558,1"⟩,
  ⟨25, 151, 0, "0,7,500,1"⟩,
  ⟨24, 151, 1, "0,2,8,1,346,1"⟩,
  ⟨24, 151, 2, "0,23,324,1"⟩,
  ⟨23, 151, 0, "0,1,8,1,17,1,188,1"⟩,
  ⟨23, 151, 1, "0,2,13,1,292,1"⟩,
  ⟨22, 151, 0, "0,1,17,1,267,1"⟩,
  ⟨20, 151, 0, "13,2,23,1,75,1"⟩,
  ⟨19, 151, 1, "13,2,23,1,76,1"⟩,
  ⟨18, 151, 0, "69,1,138,1"⟩,
  ⟨18, 151, 1, "0,1,561,1"⟩,
  ⟨17, 151, 0, "568,1"⟩,
  ⟨17, 151, 1, "1,1,552,1"⟩,
  ⟨17, 151, 2, "0,4,533,1"⟩,
  ⟨16, 151, 0, "0,3,540,1"⟩,
  ⟨14, 151, 0, "8,1,69,1,80,1"⟩,
  ⟨14, 151, 1, "0,1,8,1,366,1"⟩,
  ⟨14, 151, 2, "0,1,3,1,484,1"⟩,
  ⟨13, 151, 0, "8,1,373,1"⟩,
  ⟨13, 151, 1, "1,1,3,1,477,1"⟩,
  ⟨13, 151, 2, "0,1,8,1,367,1"⟩,
  ⟨13, 151, 3, "0,1,3,1,485,1"⟩,
  ⟨12, 151, 0, "569,1"⟩,
  ⟨12, 151, 1, "0,1,562,1"⟩,
  ⟨12, 151, 2, "0,1,43,1,191,1"⟩,
  ⟨12, 151, 3, "0,1,2,1,521,1"⟩,
  ⟨11, 151, 0, "570,1"⟩,
  ⟨11, 151, 2, "0,1,2,1,523,1"⟩,
  ⟨11, 151, 3, "0,3,546,1"⟩,
  ⟨10, 151, 2, "0,1,7,1,394,1"⟩,
  ⟨10, 151, 3, "0,1,2,1,524,1"⟩,
  ⟨10, 151, 4, "0,5,526,1"⟩,
  ⟨9, 151, 2, "0,1,7,1,396,1"⟩,
  ⟨9, 151, 3, "0,1,3,2,398,1"⟩,
  ⟨9, 151, 4, "0,7,7,1,324,1"⟩,
  ⟨8, 151, 0, "18,1,264,1"⟩,
  ⟨8, 151, 2, "0,1,7,1,398,1"⟩,
  ⟨8, 151, 3, "0,2,9,1,69,2"⟩,
  ⟨7, 151, 0, "0,1,2,1,526,1"⟩,
  ⟨7, 151, 1, "0,2,9,1,324,1"⟩,
  ⟨6, 151, 0, "0,1,10,1,324,1"⟩,
  ⟨152, 152, 0, "0,152"⟩,
  ⟨50, 152, 0, "0,2,553,1"⟩,
  ⟨49, 152, 1, "0,2,554,1"⟩,
  ⟨46, 152, 0, "0,2,8,2,236,1"⟩,
  ⟨45, 152, 0, "0,2,8,1,16,1,183,1"⟩,
  ⟨40, 152, 0, "0,2,555,1"⟩,
  ⟨39, 152, 0, "0,2,556,1"⟩,
  ⟨36, 152, 0, "0,5,17,2,138,1"⟩,
  ⟨35, 152, 0, "0,2,8,2,238,1"⟩,
  ⟨32, 152, 0, "8,2,244,1"⟩,
  ⟨31, 152, 0, "16,1,17,1,149,1"⟩,
  ⟨30, 152, 0, "8,2,245,1"⟩,
  ⟨30, 152, 1, "0,2,64,1,137,1"⟩,
  ⟨29, 152, 0, "8,2,247,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row4087_mem, Shared.BasisChunk003.row4088_mem, Shared.BasisChunk003.row4089_mem, Shared.BasisChunk003.row4090_mem, Shared.BasisChunk003.row4091_mem, Shared.BasisChunk003.row4092_mem, Shared.BasisChunk003.row4093_mem, Shared.BasisChunk003.row4095_mem, Shared.BasisChunk004.row4096_mem, Shared.BasisChunk004.row4097_mem, Shared.BasisChunk004.row4098_mem, Shared.BasisChunk004.row4099_mem, Shared.BasisChunk004.row4100_mem, Shared.BasisChunk004.row4102_mem, Shared.BasisChunk004.row4103_mem, Shared.BasisChunk004.row4104_mem, Shared.BasisChunk004.row4105_mem, Shared.BasisChunk004.row4106_mem, Shared.BasisChunk004.row4107_mem, Shared.BasisChunk004.row4108_mem, Shared.BasisChunk004.row4110_mem, Shared.BasisChunk004.row4111_mem, Shared.BasisChunk004.row4112_mem, Shared.BasisChunk004.row4113_mem, Shared.BasisChunk004.row4114_mem, Shared.BasisChunk004.row4115_mem, Shared.BasisChunk004.row4116_mem, Shared.BasisChunk004.row4117_mem, Shared.BasisChunk004.row4118_mem, Shared.BasisChunk004.row4119_mem, Shared.BasisChunk004.row4120_mem, Shared.BasisChunk004.row4121_mem, Shared.BasisChunk004.row4123_mem, Shared.BasisChunk004.row4124_mem, Shared.BasisChunk004.row4127_mem, Shared.BasisChunk004.row4128_mem, Shared.BasisChunk004.row4129_mem, Shared.BasisChunk004.row4132_mem, Shared.BasisChunk004.row4133_mem, Shared.BasisChunk004.row4134_mem, Shared.BasisChunk004.row4135_mem, Shared.BasisChunk004.row4137_mem, Shared.BasisChunk004.row4138_mem, Shared.BasisChunk004.row4139_mem, Shared.BasisChunk004.row4140_mem, Shared.BasisChunk004.row4141_mem, Shared.BasisChunk004.row4142_mem, Shared.BasisChunk004.row4143_mem, Shared.BasisChunk004.row4145_mem, Shared.BasisChunk004.row4146_mem, Shared.BasisChunk004.row4147_mem, Shared.BasisChunk004.row4148_mem, Shared.BasisChunk004.row4149_mem, Shared.BasisChunk004.row4150_mem, Shared.BasisChunk004.row4151_mem, Shared.BasisChunk004.row4153_mem, Shared.BasisChunk004.row4154_mem, Shared.BasisChunk004.row4155_mem, Shared.BasisChunk004.row4156_mem, Shared.BasisChunk004.row4157_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard053
