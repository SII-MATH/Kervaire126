module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard000
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard000
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
  exact ⟨Shared.RelationChunk000.relation3_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2 128 := by cbv
private def targetRows : List BasisRow := [⟨1, 1, 0, "0,1"⟩,
  ⟨2, 2, 0, "0,2"⟩,
  ⟨3, 3, 0, "0,3"⟩,
  ⟨4, 4, 0, "0,4"⟩,
  ⟨1, 4, 0, "2,1"⟩,
  ⟨5, 5, 0, "0,5"⟩,
  ⟨2, 5, 0, "0,1,2,1"⟩,
  ⟨6, 6, 0, "0,6"⟩,
  ⟨3, 6, 0, "0,2,2,1"⟩,
  ⟨7, 7, 0, "0,7"⟩,
  ⟨8, 8, 0, "0,8"⟩,
  ⟨2, 8, 0, "2,2"⟩,
  ⟨9, 9, 0, "0,9"⟩,
  ⟨2, 9, 0, "0,1,3,1"⟩,
  ⟨10, 10, 0, "0,10"⟩,
  ⟨3, 10, 0, "0,2,3,1"⟩,
  ⟨11, 11, 0, "0,11"⟩,
  ⟨4, 11, 0, "0,3,3,1"⟩,
  ⟨12, 12, 0, "0,12"⟩,
  ⟨3, 12, 0, "1,2,3,1"⟩,
  ⟨13, 13, 0, "0,13"⟩,
  ⟨4, 13, 0, "1,1,4,1"⟩,
  ⟨14, 14, 0, "0,14"⟩,
  ⟨15, 15, 0, "0,15"⟩,
  ⟨16, 16, 0, "0,16"⟩,
  ⟨5, 16, 0, "6,1"⟩,
  ⟨2, 16, 0, "3,2"⟩,
  ⟨17, 17, 0, "0,17"⟩,
  ⟨6, 17, 0, "0,1,6,1"⟩,
  ⟨3, 17, 0, "0,1,3,2"⟩,
  ⟨2, 17, 0, "0,1,7,1"⟩,
  ⟨18, 18, 0, "0,18"⟩,
  ⟨7, 18, 0, "0,2,6,1"⟩,
  ⟨3, 18, 0, "0,2,7,1"⟩,
  ⟨19, 19, 0, "0,19"⟩,
  ⟨5, 19, 0, "0,1,8,1"⟩,
  ⟨4, 19, 0, "0,3,7,1"⟩,
  ⟨20, 20, 0, "0,20"⟩,
  ⟨6, 20, 0, "0,2,8,1"⟩,
  ⟨5, 20, 1, "0,4,7,1"⟩,
  ⟨2, 20, 0, "2,1,7,1"⟩,
  ⟨21, 21, 0, "0,21"⟩,
  ⟨6, 21, 0, "0,5,7,1"⟩,
  ⟨3, 21, 0, "0,1,2,1,7,1"⟩,
  ⟨22, 22, 0, "0,22"⟩,
  ⟨7, 22, 0, "0,6,7,1"⟩,
  ⟨5, 22, 0, "0,1,9,1"⟩,
  ⟨4, 22, 0, "10,1"⟩,
  ⟨4, 22, 1, "0,2,2,1,7,1"⟩,
  ⟨3, 22, 0, "11,1"⟩,
  ⟨23, 23, 0, "0,23"⟩,
  ⟨8, 23, 0, "0,7,7,1"⟩,
  ⟨6, 23, 0, "0,2,9,1"⟩,
  ⟨5, 23, 0, "0,1,10,1"⟩,
  ⟨24, 24, 0, "0,24"⟩,
  ⟨7, 24, 0, "0,3,9,1"⟩,
  ⟨3, 24, 0, "2,2,7,1"⟩,
  ⟨25, 25, 0, "0,25"⟩,
  ⟨8, 25, 0, "1,1,12,1"⟩,
  ⟨5, 25, 0, "0,1,13,1"⟩,
  ⟨26, 26, 0, "0,26"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row1_mem, Shared.BasisChunk000.row2_mem, Shared.BasisChunk000.row4_mem, Shared.BasisChunk000.row5_mem, Shared.BasisChunk000.row7_mem, Shared.BasisChunk000.row8_mem, Shared.BasisChunk000.row9_mem, Shared.BasisChunk000.row10_mem, Shared.BasisChunk000.row11_mem, Shared.BasisChunk000.row12_mem, Shared.BasisChunk000.row13_mem, Shared.BasisChunk000.row14_mem, Shared.BasisChunk000.row16_mem, Shared.BasisChunk000.row17_mem, Shared.BasisChunk000.row18_mem, Shared.BasisChunk000.row19_mem, Shared.BasisChunk000.row21_mem, Shared.BasisChunk000.row22_mem, Shared.BasisChunk000.row24_mem, Shared.BasisChunk000.row25_mem, Shared.BasisChunk000.row26_mem, Shared.BasisChunk000.row27_mem, Shared.BasisChunk000.row28_mem, Shared.BasisChunk000.row30_mem, Shared.BasisChunk000.row31_mem, Shared.BasisChunk000.row33_mem, Shared.BasisChunk000.row34_mem, Shared.BasisChunk000.row36_mem, Shared.BasisChunk000.row37_mem, Shared.BasisChunk000.row38_mem, Shared.BasisChunk000.row39_mem, Shared.BasisChunk000.row40_mem, Shared.BasisChunk000.row41_mem, Shared.BasisChunk000.row43_mem, Shared.BasisChunk000.row45_mem, Shared.BasisChunk000.row46_mem, Shared.BasisChunk000.row47_mem, Shared.BasisChunk000.row48_mem, Shared.BasisChunk000.row49_mem, Shared.BasisChunk000.row51_mem, Shared.BasisChunk000.row53_mem, Shared.BasisChunk000.row54_mem, Shared.BasisChunk000.row55_mem, Shared.BasisChunk000.row57_mem, Shared.BasisChunk000.row58_mem, Shared.BasisChunk000.row59_mem, Shared.BasisChunk000.row61_mem, Shared.BasisChunk000.row62_mem, Shared.BasisChunk000.row63_mem, Shared.BasisChunk000.row64_mem, Shared.BasisChunk000.row65_mem, Shared.BasisChunk000.row66_mem, Shared.BasisChunk000.row68_mem, Shared.BasisChunk000.row69_mem, Shared.BasisChunk000.row70_mem, Shared.BasisChunk000.row71_mem, Shared.BasisChunk000.row73_mem, Shared.BasisChunk000.row74_mem, Shared.BasisChunk000.row75_mem, Shared.BasisChunk000.row76_mem, Shared.BasisChunk000.row77_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard000
