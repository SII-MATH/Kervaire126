import KIP126.LinProgram.Generated.Naturality.Words200.Shard124
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk053
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk054
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk009

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard124
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard124
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
  exact ⟨Shared.RelationChunk000.relation13_zero, Shared.RelationChunk008.relation468_zero, Shared.RelationChunk008.relation469_zero, Shared.RelationChunk053.relation1830_zero, Shared.RelationChunk053.relation1831_zero, Shared.RelationChunk054.relation1888_zero, Shared.RelationChunk054.relation1889_zero, Shared.RelationChunk054.relation1890_zero, Shared.RelationChunk054.relation1891_zero, Shared.RelationChunk054.relation1892_zero, Shared.RelationChunk054.relation1893_zero, Shared.RelationChunk054.relation1894_zero, Shared.RelationChunk054.relation1895_zero, Shared.RelationChunk054.relation1896_zero, Shared.RelationChunk054.relation1897_zero, Shared.RelationChunk054.relation1898_zero, Shared.RelationChunk054.relation1899_zero, Shared.RelationChunk054.relation1900_zero, Shared.RelationChunk054.relation1901_zero, Shared.RelationChunk054.relation1902_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 15874 79 := by cbv
private def targetRows : List BasisRow := [⟨16, 198, 0, "1157,1"⟩,
  ⟨16, 198, 1, "3,1,1020,1"⟩,
  ⟨16, 198, 2, "2,1,1088,1"⟩,
  ⟨16, 198, 3, "1,2,1090,1"⟩,
  ⟨16, 198, 4, "0,1,1131,1"⟩,
  ⟨16, 198, 5, "0,2,2,1,1057,1"⟩,
  ⟨15, 198, 1, "67,1,392,1"⟩,
  ⟨15, 198, 2, "0,1,1133,1"⟩,
  ⟨15, 198, 3, "0,1,1132,1"⟩,
  ⟨14, 198, 1, "67,1,397,1"⟩,
  ⟨14, 198, 2, "0,1,1135,1"⟩,
  ⟨14, 198, 3, "0,2,1118,1"⟩,
  ⟨13, 198, 0, "1160,1"⟩,
  ⟨13, 198, 2, "0,1,1136,1"⟩,
  ⟨13, 198, 3, "0,2,1120,1"⟩,
  ⟨12, 198, 0, "1161,1"⟩,
  ⟨12, 198, 1, "0,1,1138,1"⟩,
  ⟨12, 198, 2, "0,1,79,1,324,1"⟩,
  ⟨11, 198, 2, "0,1,80,1,324,1"⟩,
  ⟨10, 198, 0, "1164,1"⟩,
  ⟨10, 198, 2, "0,6,1058,1"⟩,
  ⟨9, 198, 1, "83,1,324,1"⟩,
  ⟨9, 198, 3, "0,6,18,2,324,1"⟩,
  ⟨8, 198, 0, "1166,1"⟩,
  ⟨8, 198, 3, "0,1,2,1,18,1,660,1"⟩,
  ⟨7, 198, 0, "86,1,324,1"⟩,
  ⟨7, 198, 1, "2,1,18,2,341,1"⟩,
  ⟨7, 198, 2, "0,2,2,1,1058,1"⟩,
  ⟨6, 198, 0, "0,2,2,1,18,2,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk009.row9429_mem, Shared.BasisChunk009.row9430_mem, Shared.BasisChunk009.row9431_mem, Shared.BasisChunk009.row9432_mem, Shared.BasisChunk009.row9433_mem, Shared.BasisChunk009.row9434_mem, Shared.BasisChunk009.row9436_mem, Shared.BasisChunk009.row9437_mem, Shared.BasisChunk009.row9438_mem, Shared.BasisChunk009.row9440_mem, Shared.BasisChunk009.row9441_mem, Shared.BasisChunk009.row9442_mem, Shared.BasisChunk009.row9443_mem, Shared.BasisChunk009.row9445_mem, Shared.BasisChunk009.row9446_mem, Shared.BasisChunk009.row9447_mem, Shared.BasisChunk009.row9448_mem, Shared.BasisChunk009.row9449_mem, Shared.BasisChunk009.row9452_mem, Shared.BasisChunk009.row9453_mem, Shared.BasisChunk009.row9455_mem, Shared.BasisChunk009.row9457_mem, Shared.BasisChunk009.row9459_mem, Shared.BasisChunk009.row9460_mem, Shared.BasisChunk009.row9463_mem, Shared.BasisChunk009.row9464_mem, Shared.BasisChunk009.row9465_mem, Shared.BasisChunk009.row9466_mem, Shared.BasisChunk009.row9467_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard124
