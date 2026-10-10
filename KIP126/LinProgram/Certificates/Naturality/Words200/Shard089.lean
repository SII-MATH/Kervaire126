import KIP126.LinProgram.Generated.Naturality.Words200.Shard089
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk032
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard089
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard089
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
  exact ⟨Shared.RelationChunk000.relation2_zero, Shared.RelationChunk000.relation5_zero, Shared.RelationChunk000.relation53_zero, Shared.RelationChunk000.relation54_zero, Shared.RelationChunk000.relation55_zero, Shared.RelationChunk000.relation111_zero, Shared.RelationChunk003.relation287_zero, Shared.RelationChunk019.relation912_zero, Shared.RelationChunk019.relation913_zero, Shared.RelationChunk031.relation1322_zero, Shared.RelationChunk031.relation1323_zero, Shared.RelationChunk031.relation1324_zero, Shared.RelationChunk032.relation1325_zero, Shared.RelationChunk032.relation1326_zero, Shared.RelationChunk032.relation1327_zero, Shared.RelationChunk032.relation1359_zero, Shared.RelationChunk032.relation1360_zero, Shared.RelationChunk032.relation1361_zero, Shared.RelationChunk032.relation1362_zero, Shared.RelationChunk032.relation1363_zero, Shared.RelationChunk032.relation1364_zero, Shared.RelationChunk032.relation1365_zero, Shared.RelationChunk032.relation1367_zero, Shared.RelationChunk032.relation1368_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11394 128 := by cbv
private def targetRows : List BasisRow := [⟨35, 178, 0, "0,1,8,1,637,1"⟩,
  ⟨35, 178, 1, "0,2,17,1,516,1"⟩,
  ⟨29, 178, 0, "863,1"⟩,
  ⟨28, 178, 0, "8,1,642,1"⟩,
  ⟨27, 178, 0, "864,1"⟩,
  ⟨26, 178, 0, "13,1,585,1"⟩,
  ⟨26, 178, 1, "13,3,23,1,83,1"⟩,
  ⟨26, 178, 2, "0,1,853,1"⟩,
  ⟨26, 178, 3, "0,2,8,1,627,1"⟩,
  ⟨25, 178, 0, "9,1,13,3,133,1"⟩,
  ⟨25, 178, 1, "1,1,8,1,627,1"⟩,
  ⟨25, 178, 2, "0,1,855,1"⟩,
  ⟨25, 178, 3, "0,2,832,1"⟩,
  ⟨24, 178, 0, "0,1,856,1"⟩,
  ⟨22, 178, 1, "0,1,7,1,655,1"⟩,
  ⟨21, 178, 0, "1,1,79,1,209,1"⟩,
  ⟨21, 178, 1, "0,1,8,1,17,1,333,1"⟩,
  ⟨21, 178, 2, "0,2,64,1,235,1"⟩,
  ⟨21, 178, 3, "0,10,743,1"⟩,
  ⟨20, 178, 0, "13,2,335,1"⟩,
  ⟨20, 178, 1, "0,1,64,1,239,1"⟩,
  ⟨20, 178, 2, "0,2,837,1"⟩,
  ⟨20, 178, 3, "0,2,836,1"⟩,
  ⟨19, 178, 0, "9,1,619,1"⟩,
  ⟨19, 178, 2, "0,2,838,1"⟩,
  ⟨18, 178, 3, "0,3,825,1"⟩,
  ⟨17, 178, 1, "9,1,13,1,373,1"⟩,
  ⟨17, 178, 3, "0,2,841,1"⟩,
  ⟨16, 178, 1, "0,2,843,1"⟩,
  ⟨16, 178, 2, "0,2,18,1,502,1"⟩,
  ⟨15, 178, 0, "43,1,336,1"⟩,
  ⟨15, 178, 1, "2,1,814,1"⟩,
  ⟨15, 178, 4, "0,2,845,1"⟩,
  ⟨15, 178, 5, "0,2,8,1,16,1,324,1"⟩,
  ⟨14, 178, 1, "867,1"⟩,
  ⟨14, 178, 2, "2,1,815,1"⟩,
  ⟨14, 178, 3, "0,1,859,1"⟩,
  ⟨14, 178, 4, "0,1,858,1"⟩,
  ⟨14, 178, 5, "0,1,43,1,333,1"⟩,
  ⟨14, 178, 6, "0,2,8,1,17,1,324,1"⟩,
  ⟨13, 178, 0, "3,1,769,1"⟩,
  ⟨13, 178, 1, "2,1,817,1"⟩,
  ⟨13, 178, 2, "2,1,816,1"⟩,
  ⟨13, 178, 3, "0,1,861,1"⟩,
  ⟨13, 178, 4, "0,1,3,1,755,1"⟩,
  ⟨12, 178, 1, "0,1,3,1,757,1"⟩,
  ⟨12, 178, 2, "0,1,3,1,756,1"⟩,
  ⟨12, 178, 3, "0,2,846,1"⟩,
  ⟨11, 178, 0, "3,1,771,1"⟩,
  ⟨11, 178, 2, "0,1,2,1,802,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6805_mem, Shared.BasisChunk006.row6806_mem, Shared.BasisChunk006.row6807_mem, Shared.BasisChunk006.row6809_mem, Shared.BasisChunk006.row6810_mem, Shared.BasisChunk006.row6811_mem, Shared.BasisChunk006.row6812_mem, Shared.BasisChunk006.row6813_mem, Shared.BasisChunk006.row6814_mem, Shared.BasisChunk006.row6815_mem, Shared.BasisChunk006.row6816_mem, Shared.BasisChunk006.row6817_mem, Shared.BasisChunk006.row6818_mem, Shared.BasisChunk006.row6819_mem, Shared.BasisChunk006.row6821_mem, Shared.BasisChunk006.row6822_mem, Shared.BasisChunk006.row6823_mem, Shared.BasisChunk006.row6824_mem, Shared.BasisChunk006.row6825_mem, Shared.BasisChunk006.row6826_mem, Shared.BasisChunk006.row6827_mem, Shared.BasisChunk006.row6828_mem, Shared.BasisChunk006.row6829_mem, Shared.BasisChunk006.row6830_mem, Shared.BasisChunk006.row6832_mem, Shared.BasisChunk006.row6836_mem, Shared.BasisChunk006.row6838_mem, Shared.BasisChunk006.row6840_mem, Shared.BasisChunk006.row6842_mem, Shared.BasisChunk006.row6843_mem, Shared.BasisChunk006.row6844_mem, Shared.BasisChunk006.row6845_mem, Shared.BasisChunk006.row6848_mem, Shared.BasisChunk006.row6849_mem, Shared.BasisChunk006.row6851_mem, Shared.BasisChunk006.row6852_mem, Shared.BasisChunk006.row6853_mem, Shared.BasisChunk006.row6854_mem, Shared.BasisChunk006.row6855_mem, Shared.BasisChunk006.row6856_mem, Shared.BasisChunk006.row6857_mem, Shared.BasisChunk006.row6858_mem, Shared.BasisChunk006.row6859_mem, Shared.BasisChunk006.row6860_mem, Shared.BasisChunk006.row6861_mem, Shared.BasisChunk006.row6863_mem, Shared.BasisChunk006.row6864_mem, Shared.BasisChunk006.row6865_mem, Shared.BasisChunk006.row6866_mem, Shared.BasisChunk006.row6868_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard089
