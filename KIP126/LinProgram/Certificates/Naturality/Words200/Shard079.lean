module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard079
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard079
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard079
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
  exact ⟨Shared.RelationChunk026.relation1130_zero, Shared.RelationChunk026.relation1131_zero, Shared.RelationChunk026.relation1132_zero, Shared.RelationChunk026.relation1133_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10114 128 := by cbv
private def targetRows : List BasisRow := [⟨15, 171, 2, "0,1,767,1"⟩,
  ⟨15, 171, 3, "0,1,766,1"⟩,
  ⟨15, 171, 4, "0,1,67,1,203,1"⟩,
  ⟨14, 171, 0, "74,1,197,1"⟩,
  ⟨14, 171, 1, "9,1,563,1"⟩,
  ⟨14, 171, 2, "1,1,76,1,190,1"⟩,
  ⟨14, 171, 3, "0,1,68,1,203,1"⟩,
  ⟨14, 171, 4, "0,1,31,1,324,1"⟩,
  ⟨14, 171, 5, "0,1,3,1,673,1"⟩,
  ⟨14, 171, 6, "0,3,743,1"⟩,
  ⟨13, 171, 0, "2,1,732,1"⟩,
  ⟨13, 171, 1, "0,1,769,1"⟩,
  ⟨13, 171, 2, "0,1,3,1,674,1"⟩,
  ⟨13, 171, 3, "0,1,2,1,719,1"⟩,
  ⟨13, 171, 4, "0,2,755,1"⟩,
  ⟨13, 171, 5, "0,11,18,1,324,1"⟩,
  ⟨12, 171, 0, "2,1,734,1"⟩,
  ⟨12, 171, 1, "0,1,770,1"⟩,
  ⟨12, 171, 2, "0,2,757,1"⟩,
  ⟨11, 171, 1, "0,1,772,1"⟩,
  ⟨11, 171, 2, "0,1,18,1,443,1"⟩,
  ⟨10, 171, 0, "3,1,18,1,352,1"⟩,
  ⟨10, 171, 1, "0,1,18,1,445,1"⟩,
  ⟨10, 171, 2, "0,1,8,1,13,1,324,1"⟩,
  ⟨10, 171, 3, "0,3,747,1"⟩,
  ⟨9, 171, 1, "0,1,32,1,324,1"⟩,
  ⟨9, 171, 2, "0,3,749,1"⟩,
  ⟨8, 171, 0, "0,1,18,1,446,1"⟩,
  ⟨8, 171, 1, "0,3,750,1"⟩,
  ⟨7, 171, 0, "0,1,34,1,324,1"⟩,
  ⟨7, 171, 1, "0,3,751,1"⟩,
  ⟨6, 171, 0, "0,3,3,1,18,1,324,1"⟩,
  ⟨172, 172, 0, "0,172"⟩,
  ⟨57, 172, 0, "783,1"⟩,
  ⟨53, 172, 0, "0,1,8,1,578,1"⟩,
  ⟨52, 172, 0, "0,1,8,1,579,1"⟩,
  ⟨51, 172, 0, "0,1,17,1,470,1"⟩,
  ⟨46, 172, 0, "0,8,686,1"⟩,
  ⟨45, 172, 0, "0,44,324,1"⟩,
  ⟨43, 172, 0, "0,1,8,2,402,1"⟩,
  ⟨42, 172, 0, "0,1,8,2,403,1"⟩,
  ⟨42, 172, 1, "0,2,16,1,452,1"⟩,
  ⟨41, 172, 0, "0,1,16,1,17,1,225,1"⟩,
  ⟨41, 172, 1, "0,2,17,1,452,1"⟩,
  ⟨40, 172, 0, "0,1,17,2,225,1"⟩,
  ⟨39, 172, 0, "0,5,725,1"⟩,
  ⟨38, 172, 0, "0,3,752,1"⟩,
  ⟨36, 172, 0, "0,2,759,1"⟩,
  ⟨35, 172, 0, "0,1,778,1"⟩,
  ⟨32, 172, 0, "0,2,8,2,380,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row6069_mem, Shared.BasisChunk005.row6070_mem, Shared.BasisChunk005.row6071_mem, Shared.BasisChunk005.row6072_mem, Shared.BasisChunk005.row6073_mem, Shared.BasisChunk005.row6074_mem, Shared.BasisChunk005.row6075_mem, Shared.BasisChunk005.row6076_mem, Shared.BasisChunk005.row6077_mem, Shared.BasisChunk005.row6078_mem, Shared.BasisChunk005.row6079_mem, Shared.BasisChunk005.row6080_mem, Shared.BasisChunk005.row6081_mem, Shared.BasisChunk005.row6082_mem, Shared.BasisChunk005.row6083_mem, Shared.BasisChunk005.row6084_mem, Shared.BasisChunk005.row6085_mem, Shared.BasisChunk005.row6086_mem, Shared.BasisChunk005.row6087_mem, Shared.BasisChunk005.row6089_mem, Shared.BasisChunk005.row6090_mem, Shared.BasisChunk005.row6091_mem, Shared.BasisChunk005.row6092_mem, Shared.BasisChunk005.row6093_mem, Shared.BasisChunk005.row6094_mem, Shared.BasisChunk005.row6096_mem, Shared.BasisChunk005.row6097_mem, Shared.BasisChunk005.row6098_mem, Shared.BasisChunk005.row6099_mem, Shared.BasisChunk005.row6100_mem, Shared.BasisChunk005.row6101_mem, Shared.BasisChunk005.row6102_mem, Shared.BasisChunk005.row6104_mem, Shared.BasisChunk005.row6106_mem, Shared.BasisChunk005.row6107_mem, Shared.BasisChunk005.row6108_mem, Shared.BasisChunk005.row6109_mem, Shared.BasisChunk005.row6110_mem, Shared.BasisChunk005.row6111_mem, Shared.BasisChunk005.row6112_mem, Shared.BasisChunk005.row6113_mem, Shared.BasisChunk005.row6114_mem, Shared.BasisChunk005.row6115_mem, Shared.BasisChunk005.row6116_mem, Shared.BasisChunk005.row6117_mem, Shared.BasisChunk005.row6118_mem, Shared.BasisChunk005.row6119_mem, Shared.BasisChunk005.row6120_mem, Shared.BasisChunk005.row6121_mem, Shared.BasisChunk005.row6122_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard079
