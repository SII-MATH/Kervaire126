module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard056
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard056
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard056
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
  exact ⟨Shared.RelationChunk001.relation189_zero, Shared.RelationChunk003.relation287_zero, Shared.RelationChunk016.relation802_zero, Shared.RelationChunk016.relation803_zero, Shared.RelationChunk016.relation804_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7170 128 := by cbv
private def targetRows : List BasisRow := [⟨154, 154, 0, "0,154"⟩,
  ⟨51, 154, 0, "0,4,554,1"⟩,
  ⟨49, 154, 0, "0,1,578,1"⟩,
  ⟨48, 154, 0, "0,1,579,1"⟩,
  ⟨39, 154, 0, "0,1,8,1,402,1"⟩,
  ⟨38, 154, 0, "0,1,8,1,403,1"⟩,
  ⟨35, 154, 0, "0,1,8,2,16,1,137,1"⟩,
  ⟨34, 154, 1, "0,1,8,2,16,1,138,1"⟩,
  ⟨32, 154, 0, "0,4,64,1,137,1"⟩,
  ⟨31, 154, 0, "0,4,64,1,138,1"⟩,
  ⟨30, 154, 1, "0,5,17,1,260,1"⟩,
  ⟨29, 154, 0, "0,1,64,1,146,1"⟩,
  ⟨29, 154, 1, "0,4,558,1"⟩,
  ⟨28, 154, 0, "0,1,64,1,147,1"⟩,
  ⟨28, 154, 1, "0,2,8,1,380,1"⟩,
  ⟨28, 154, 2, "0,10,500,1"⟩,
  ⟨27, 154, 0, "0,1,8,1,404,1"⟩,
  ⟨27, 154, 1, "0,2,17,1,278,1"⟩,
  ⟨27, 154, 2, "0,26,324,1"⟩,
  ⟨23, 154, 0, "0,1,8,1,20,1,188,1"⟩,
  ⟨22, 154, 1, "13,2,23,1,83,1"⟩,
  ⟨21, 154, 1, "9,1,13,2,133,1"⟩,
  ⟨21, 154, 2, "0,3,69,1,138,1"⟩,
  ⟨20, 154, 1, "0,3,568,1"⟩,
  ⟨18, 154, 0, "69,1,147,1"⟩,
  ⟨18, 154, 1, "0,1,582,1"⟩,
  ⟨17, 154, 0, "588,1"⟩,
  ⟨16, 154, 0, "13,1,335,1"⟩,
  ⟨15, 154, 0, "8,1,69,1,89,1"⟩,
  ⟨15, 154, 1, "0,4,562,1"⟩,
  ⟨14, 154, 0, "8,1,419,1"⟩,
  ⟨14, 154, 1, "0,1,8,1,414,1"⟩,
  ⟨14, 154, 2, "0,2,575,1"⟩,
  ⟨13, 154, 0, "589,1"⟩,
  ⟨13, 154, 1, "9,1,373,1"⟩,
  ⟨13, 154, 3, "0,1,8,1,415,1"⟩,
  ⟨12, 154, 1, "0,1,583,1"⟩,
  ⟨12, 154, 2, "0,2,3,1,504,1"⟩,
  ⟨11, 154, 2, "1,1,3,1,504,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4322_mem, Shared.BasisChunk004.row4323_mem, Shared.BasisChunk004.row4325_mem, Shared.BasisChunk004.row4326_mem, Shared.BasisChunk004.row4327_mem, Shared.BasisChunk004.row4328_mem, Shared.BasisChunk004.row4330_mem, Shared.BasisChunk004.row4332_mem, Shared.BasisChunk004.row4333_mem, Shared.BasisChunk004.row4334_mem, Shared.BasisChunk004.row4336_mem, Shared.BasisChunk004.row4337_mem, Shared.BasisChunk004.row4338_mem, Shared.BasisChunk004.row4339_mem, Shared.BasisChunk004.row4340_mem, Shared.BasisChunk004.row4341_mem, Shared.BasisChunk004.row4342_mem, Shared.BasisChunk004.row4343_mem, Shared.BasisChunk004.row4344_mem, Shared.BasisChunk004.row4345_mem, Shared.BasisChunk004.row4347_mem, Shared.BasisChunk004.row4349_mem, Shared.BasisChunk004.row4350_mem, Shared.BasisChunk004.row4352_mem, Shared.BasisChunk004.row4355_mem, Shared.BasisChunk004.row4356_mem, Shared.BasisChunk004.row4357_mem, Shared.BasisChunk004.row4358_mem, Shared.BasisChunk004.row4359_mem, Shared.BasisChunk004.row4360_mem, Shared.BasisChunk004.row4361_mem, Shared.BasisChunk004.row4362_mem, Shared.BasisChunk004.row4363_mem, Shared.BasisChunk004.row4364_mem, Shared.BasisChunk004.row4365_mem, Shared.BasisChunk004.row4367_mem, Shared.BasisChunk004.row4369_mem, Shared.BasisChunk004.row4370_mem, Shared.BasisChunk004.row4373_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard056
