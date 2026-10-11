module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard113
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk048
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard113
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard113
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
  exact ⟨Shared.RelationChunk005.relation360_zero, Shared.RelationChunk005.relation361_zero, Shared.RelationChunk048.relation1762_zero, Shared.RelationChunk048.relation1763_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14466 128 := by cbv
private def targetRows : List BasisRow := [⟨53, 193, 0, "0,5,969,1"⟩,
  ⟨52, 193, 0, "0,4,17,1,636,1"⟩,
  ⟨51, 193, 0, "0,1,8,1,805,1"⟩,
  ⟨50, 193, 0, "0,1,8,1,806,1"⟩,
  ⟨50, 193, 1, "0,2,1030,1"⟩,
  ⟨49, 193, 0, "0,1,17,1,663,1"⟩,
  ⟨44, 193, 0, "0,2,1033,1"⟩,
  ⟨43, 193, 0, "1059,1"⟩,
  ⟨41, 193, 0, "0,1,8,1,64,1,224,1"⟩,
  ⟨40, 193, 0, "0,1,8,1,64,1,225,1"⟩,
  ⟨40, 193, 1, "0,2,8,1,16,1,491,1"⟩,
  ⟨39, 193, 1, "0,2,8,1,17,1,491,1"⟩,
  ⟨37, 193, 0, "0,10,919,1"⟩,
  ⟨36, 193, 1, "0,11,898,1"⟩,
  ⟨34, 193, 1, "0,4,64,3"⟩,
  ⟨33, 193, 0, "1061,1"⟩,
  ⟨33, 193, 1, "0,4,64,1,299,1"⟩,
  ⟨32, 193, 0, "8,1,820,1"⟩,
  ⟨32, 193, 2, "0,6,963,1"⟩,
  ⟨31, 193, 0, "8,1,821,1"⟩,
  ⟨31, 193, 1, "0,4,64,1,301,1"⟩,
  ⟨31, 193, 2, "0,5,974,1"⟩,
  ⟨30, 193, 0, "9,1,784,1"⟩,
  ⟨30, 193, 1, "0,2,8,1,797,1"⟩,
  ⟨30, 193, 2, "0,5,976,1"⟩,
  ⟨29, 193, 0, "0,2,17,1,655,1"⟩,
  ⟨29, 193, 1, "0,2,2,1,963,1"⟩,
  ⟨29, 193, 2, "0,5,978,1"⟩,
  ⟨27, 193, 0, "13,5,95,1"⟩,
  ⟨26, 193, 0, "13,4,164,1"⟩,
  ⟨26, 193, 1, "0,1,2,1,978,1"⟩,
  ⟨25, 193, 0, "0,1,3,1,929,1"⟩,
  ⟨24, 193, 0, "0,1,1049,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8606_mem, Shared.BasisChunk008.row8607_mem, Shared.BasisChunk008.row8608_mem, Shared.BasisChunk008.row8609_mem, Shared.BasisChunk008.row8610_mem, Shared.BasisChunk008.row8611_mem, Shared.BasisChunk008.row8612_mem, Shared.BasisChunk008.row8613_mem, Shared.BasisChunk008.row8615_mem, Shared.BasisChunk008.row8616_mem, Shared.BasisChunk008.row8617_mem, Shared.BasisChunk008.row8619_mem, Shared.BasisChunk008.row8620_mem, Shared.BasisChunk008.row8622_mem, Shared.BasisChunk008.row8624_mem, Shared.BasisChunk008.row8625_mem, Shared.BasisChunk008.row8626_mem, Shared.BasisChunk008.row8627_mem, Shared.BasisChunk008.row8629_mem, Shared.BasisChunk008.row8630_mem, Shared.BasisChunk008.row8631_mem, Shared.BasisChunk008.row8632_mem, Shared.BasisChunk008.row8633_mem, Shared.BasisChunk008.row8634_mem, Shared.BasisChunk008.row8635_mem, Shared.BasisChunk008.row8636_mem, Shared.BasisChunk008.row8637_mem, Shared.BasisChunk008.row8638_mem, Shared.BasisChunk008.row8639_mem, Shared.BasisChunk008.row8640_mem, Shared.BasisChunk008.row8641_mem, Shared.BasisChunk008.row8642_mem, Shared.BasisChunk008.row8643_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard113
