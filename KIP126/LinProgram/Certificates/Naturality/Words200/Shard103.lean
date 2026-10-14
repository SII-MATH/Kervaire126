module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard103
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard103
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard103
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
  exact ⟨Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13186 128 := by cbv
private def targetRows : List BasisRow := [⟨61, 187, 0, "0,1,951,1"⟩,
  ⟨60, 187, 0, "0,59,324,1"⟩,
  ⟨57, 187, 0, "0,1,8,2,553,1"⟩,
  ⟨56, 187, 0, "0,1,8,2,554,1"⟩,
  ⟨54, 187, 0, "0,4,916,1"⟩,
  ⟨53, 187, 0, "0,4,917,1"⟩,
  ⟨51, 187, 0, "0,1,952,1"⟩,
  ⟨50, 187, 0, "0,1,953,1"⟩,
  ⟨47, 187, 0, "0,1,8,2,555,1"⟩,
  ⟨46, 187, 0, "0,1,8,2,556,1"⟩,
  ⟨46, 187, 1, "0,13,807,1"⟩,
  ⟨45, 187, 0, "0,1,8,1,17,1,433,1"⟩,
  ⟨45, 187, 1, "0,14,795,1"⟩,
  ⟨40, 187, 0, "0,2,8,1,725,1"⟩,
  ⟨39, 187, 0, "0,1,954,1"⟩,
  ⟨36, 187, 1, "0,2,8,2,16,1,260,1"⟩,
  ⟨35, 187, 0, "0,2,8,2,17,1,260,1"⟩,
  ⟨35, 187, 1, "0,3,149,2"⟩,
  ⟨34, 187, 0, "0,3,927,1"⟩,
  ⟨33, 187, 0, "0,5,64,1,260,1"⟩,
  ⟨32, 187, 1, "0,3,64,1,274,1"⟩,
  ⟨32, 187, 2, "0,5,897,1"⟩,
  ⟨31, 187, 0, "962,1"⟩,
  ⟨31, 187, 1, "0,4,921,1"⟩,
  ⟨31, 187, 2, "0,4,919,1"⟩,
  ⟨30, 187, 0, "8,1,753,1"⟩,
  ⟨30, 187, 1, "0,2,64,1,278,1"⟩,
  ⟨30, 187, 2, "0,5,898,1"⟩,
  ⟨29, 187, 0, "9,1,715,1"⟩,
  ⟨29, 187, 1, "0,1,956,1"⟩,
  ⟨29, 187, 2, "0,2,940,1"⟩,
  ⟨26, 187, 1, "13,5,75,1"⟩,
  ⟨26, 187, 2, "0,2,9,1,690,1"⟩,
  ⟨25, 187, 0, "13,5,76,1"⟩,
  ⟨25, 187, 1, "0,1,2,1,901,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7871_mem, Shared.BasisChunk007.row7872_mem, Shared.BasisChunk007.row7873_mem, Shared.BasisChunk007.row7874_mem, Shared.BasisChunk007.row7875_mem, Shared.BasisChunk007.row7876_mem, Shared.BasisChunk007.row7878_mem, Shared.BasisChunk007.row7879_mem, Shared.BasisChunk007.row7880_mem, Shared.BasisChunk007.row7881_mem, Shared.BasisChunk007.row7882_mem, Shared.BasisChunk007.row7883_mem, Shared.BasisChunk007.row7884_mem, Shared.BasisChunk007.row7885_mem, Shared.BasisChunk007.row7886_mem, Shared.BasisChunk007.row7888_mem, Shared.BasisChunk007.row7889_mem, Shared.BasisChunk007.row7890_mem, Shared.BasisChunk007.row7891_mem, Shared.BasisChunk007.row7892_mem, Shared.BasisChunk007.row7894_mem, Shared.BasisChunk007.row7895_mem, Shared.BasisChunk007.row7896_mem, Shared.BasisChunk007.row7897_mem, Shared.BasisChunk007.row7898_mem, Shared.BasisChunk007.row7899_mem, Shared.BasisChunk007.row7900_mem, Shared.BasisChunk007.row7901_mem, Shared.BasisChunk007.row7902_mem, Shared.BasisChunk007.row7903_mem, Shared.BasisChunk007.row7904_mem, Shared.BasisChunk007.row7906_mem, Shared.BasisChunk007.row7907_mem, Shared.BasisChunk007.row7908_mem, Shared.BasisChunk007.row7909_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard103
