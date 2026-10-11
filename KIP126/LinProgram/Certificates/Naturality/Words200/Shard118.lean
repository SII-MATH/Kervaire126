module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard118
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard118
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard118
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
  simp
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15106 128 := by cbv
private def targetRows : List BasisRow := [⟨16, 195, 2, "0,3,1057,1"⟩,
  ⟨15, 195, 0, "67,1,352,1"⟩,
  ⟨15, 195, 1, "0,1,1090,1"⟩,
  ⟨15, 195, 2, "0,4,64,1,324,1"⟩,
  ⟨14, 195, 2, "0,1,1091,1"⟩,
  ⟨14, 195, 3, "0,3,66,1,324,1"⟩,
  ⟨13, 195, 1, "1099,1"⟩,
  ⟨13, 195, 2, "1,2,64,1,324,1"⟩,
  ⟨12, 195, 0, "0,1,72,1,324,1"⟩,
  ⟨12, 195, 1, "0,2,18,1,659,1"⟩,
  ⟨11, 195, 0, "0,2,18,1,20,1,324,1"⟩,
  ⟨8, 195, 1, "0,2,18,1,660,1"⟩,
  ⟨7, 195, 0, "75,1,324,1"⟩,
  ⟨7, 195, 1, "74,1,324,1"⟩,
  ⟨7, 195, 3, "0,3,1058,1"⟩,
  ⟨6, 195, 1, "1,1,70,1,324,1"⟩,
  ⟨6, 195, 2, "0,3,18,2,324,1"⟩,
  ⟨196, 196, 0, "0,196"⟩,
  ⟨65, 196, 0, "1101,1"⟩,
  ⟨61, 196, 0, "0,1,8,1,851,1"⟩,
  ⟨60, 196, 0, "0,1,8,1,852,1"⟩,
  ⟨59, 196, 0, "0,1,17,1,701,1"⟩,
  ⟨51, 196, 0, "0,1,8,2,635,1"⟩,
  ⟨50, 196, 0, "0,1,8,2,636,1"⟩,
  ⟨50, 196, 1, "0,2,16,1,685,1"⟩,
  ⟨49, 196, 0, "0,1,16,1,17,1,403,1"⟩,
  ⟨49, 196, 1, "0,2,17,1,685,1"⟩,
  ⟨48, 196, 0, "0,1,17,2,403,1"⟩,
  ⟨47, 196, 0, "0,5,1033,1"⟩,
  ⟨46, 196, 0, "0,3,1059,1"⟩,
  ⟨44, 196, 0, "0,2,1076,1"⟩,
  ⟨43, 196, 0, "0,1,1093,1"⟩,
  ⟨40, 196, 0, "0,2,8,2,623,1"⟩,
  ⟨40, 196, 1, "0,13,919,1"⟩,
  ⟨39, 196, 0, "0,2,8,1,17,1,516,1"⟩,
  ⟨39, 196, 1, "0,14,898,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8980_mem, Shared.BasisChunk008.row8981_mem, Shared.BasisChunk008.row8982_mem, Shared.BasisChunk008.row8983_mem, Shared.BasisChunk008.row8986_mem, Shared.BasisChunk008.row8987_mem, Shared.BasisChunk008.row8989_mem, Shared.BasisChunk008.row8990_mem, Shared.BasisChunk008.row8991_mem, Shared.BasisChunk008.row8992_mem, Shared.BasisChunk008.row8993_mem, Shared.BasisChunk008.row8996_mem, Shared.BasisChunk008.row8997_mem, Shared.BasisChunk008.row8998_mem, Shared.BasisChunk008.row9000_mem, Shared.BasisChunk008.row9002_mem, Shared.BasisChunk008.row9003_mem, Shared.BasisChunk008.row9004_mem, Shared.BasisChunk008.row9006_mem, Shared.BasisChunk008.row9007_mem, Shared.BasisChunk008.row9008_mem, Shared.BasisChunk008.row9009_mem, Shared.BasisChunk008.row9010_mem, Shared.BasisChunk008.row9011_mem, Shared.BasisChunk008.row9012_mem, Shared.BasisChunk008.row9013_mem, Shared.BasisChunk008.row9014_mem, Shared.BasisChunk008.row9015_mem, Shared.BasisChunk008.row9016_mem, Shared.BasisChunk008.row9017_mem, Shared.BasisChunk008.row9018_mem, Shared.BasisChunk008.row9019_mem, Shared.BasisChunk008.row9020_mem, Shared.BasisChunk008.row9021_mem, Shared.BasisChunk008.row9022_mem, Shared.BasisChunk008.row9023_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard118
