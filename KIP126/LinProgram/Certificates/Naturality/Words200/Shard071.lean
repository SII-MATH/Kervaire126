import KIP126.LinProgram.Generated.Naturality.Words200.Shard071
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard071
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard071
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
  exact ⟨Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk002.relation223_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk005.relation361_zero, Shared.RelationChunk013.relation699_zero, Shared.RelationChunk013.relation700_zero, Shared.RelationChunk023.relation1015_zero, Shared.RelationChunk023.relation1016_zero, Shared.RelationChunk023.relation1017_zero, Shared.RelationChunk023.relation1018_zero, Shared.RelationChunk023.relation1019_zero, Shared.RelationChunk023.relation1020_zero, Shared.RelationChunk023.relation1021_zero, Shared.RelationChunk023.relation1022_zero, Shared.RelationChunk023.relation1023_zero, Shared.RelationChunk023.relation1024_zero, Shared.RelationChunk023.relation1025_zero, Shared.RelationChunk023.relation1026_zero, Shared.RelationChunk023.relation1027_zero, Shared.RelationChunk023.relation1028_zero, Shared.RelationChunk023.relation1029_zero, Shared.RelationChunk023.relation1030_zero, Shared.RelationChunk023.relation1031_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 9090 128 := by cbv
private def targetRows : List BasisRow := [⟨31, 166, 0, "0,1,8,1,529,1"⟩,
  ⟨31, 166, 1, "0,2,17,1,380,1"⟩,
  ⟨30, 166, 0, "0,6,642,1"⟩,
  ⟨29, 166, 0, "0,5,654,1"⟩,
  ⟨28, 166, 0, "0,8,627,1"⟩,
  ⟨27, 166, 0, "0,6,645,1"⟩,
  ⟨27, 166, 1, "0,6,644,1"⟩,
  ⟨24, 166, 0, "716,1"⟩,
  ⟨24, 166, 1, "13,4,83,1"⟩,
  ⟨23, 166, 0, "18,1,380,1"⟩,
  ⟨23, 166, 1, "9,1,13,3,95,1"⟩,
  ⟨23, 166, 2, "1,2,666,1"⟩,
  ⟨23, 166, 3, "0,1,64,1,187,1"⟩,
  ⟨22, 166, 0, "69,1,185,1"⟩,
  ⟨22, 166, 1, "0,1,702,1"⟩,
  ⟨22, 166, 2, "0,1,64,1,188,1"⟩,
  ⟨22, 166, 3, "0,2,690,1"⟩,
  ⟨21, 166, 0, "3,1,627,1"⟩,
  ⟨21, 166, 1, "1,1,690,1"⟩,
  ⟨21, 166, 2, "0,1,703,1"⟩,
  ⟨20, 166, 1, "2,2,628,1"⟩,
  ⟨20, 166, 2, "0,1,706,1"⟩,
  ⟨19, 166, 0, "8,2,69,1,72,1"⟩,
  ⟨19, 166, 2, "0,2,693,1"⟩,
  ⟨18, 166, 0, "23,1,335,1"⟩,
  ⟨18, 166, 1, "1,1,693,1"⟩,
  ⟨18, 166, 2, "1,1,692,1"⟩,
  ⟨18, 166, 4, "0,1,8,2,333,1"⟩,
  ⟨18, 166, 5, "0,4,671,1"⟩,
  ⟨17, 166, 0, "24,1,335,1"⟩,
  ⟨17, 166, 1, "8,2,338,1"⟩,
  ⟨17, 166, 3, "1,2,669,1"⟩,
  ⟨17, 166, 4, "0,1,707,1"⟩,
  ⟨17, 166, 5, "0,1,8,1,534,1"⟩,
  ⟨16, 166, 1, "3,1,630,1"⟩,
  ⟨16, 166, 2, "1,1,694,1"⟩,
  ⟨16, 166, 3, "0,1,708,1"⟩,
  ⟨16, 166, 4, "0,1,17,1,415,1"⟩,
  ⟨15, 166, 0, "67,1,190,1"⟩,
  ⟨15, 166, 2, "13,1,485,1"⟩,
  ⟨15, 166, 3, "0,1,709,1"⟩,
  ⟨14, 166, 0, "718,1"⟩,
  ⟨14, 166, 1, "67,1,191,1"⟩,
  ⟨13, 166, 0, "0,1,711,1"⟩,
  ⟨12, 166, 0, "0,1,712,1"⟩,
  ⟨12, 166, 1, "0,2,18,1,366,1"⟩,
  ⟨12, 166, 2, "0,4,676,1"⟩,
  ⟨11, 166, 1, "0,2,18,1,367,1"⟩,
  ⟨11, 166, 2, "0,2,8,2,324,1"⟩,
  ⟨11, 166, 3, "0,2,7,1,546,1"⟩,
  ⟨10, 166, 0, "1,1,7,1,546,1"⟩,
  ⟨10, 166, 1, "0,2,696,1"⟩,
  ⟨10, 166, 2, "0,2,22,1,324,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5452_mem, Shared.BasisChunk005.row5453_mem, Shared.BasisChunk005.row5454_mem, Shared.BasisChunk005.row5455_mem, Shared.BasisChunk005.row5456_mem, Shared.BasisChunk005.row5457_mem, Shared.BasisChunk005.row5458_mem, Shared.BasisChunk005.row5460_mem, Shared.BasisChunk005.row5461_mem, Shared.BasisChunk005.row5462_mem, Shared.BasisChunk005.row5463_mem, Shared.BasisChunk005.row5464_mem, Shared.BasisChunk005.row5465_mem, Shared.BasisChunk005.row5466_mem, Shared.BasisChunk005.row5467_mem, Shared.BasisChunk005.row5468_mem, Shared.BasisChunk005.row5469_mem, Shared.BasisChunk005.row5470_mem, Shared.BasisChunk005.row5471_mem, Shared.BasisChunk005.row5472_mem, Shared.BasisChunk005.row5474_mem, Shared.BasisChunk005.row5475_mem, Shared.BasisChunk005.row5476_mem, Shared.BasisChunk005.row5478_mem, Shared.BasisChunk005.row5479_mem, Shared.BasisChunk005.row5480_mem, Shared.BasisChunk005.row5481_mem, Shared.BasisChunk005.row5483_mem, Shared.BasisChunk005.row5484_mem, Shared.BasisChunk005.row5485_mem, Shared.BasisChunk005.row5486_mem, Shared.BasisChunk005.row5488_mem, Shared.BasisChunk005.row5489_mem, Shared.BasisChunk005.row5490_mem, Shared.BasisChunk005.row5492_mem, Shared.BasisChunk005.row5493_mem, Shared.BasisChunk005.row5494_mem, Shared.BasisChunk005.row5495_mem, Shared.BasisChunk005.row5496_mem, Shared.BasisChunk005.row5498_mem, Shared.BasisChunk005.row5499_mem, Shared.BasisChunk005.row5500_mem, Shared.BasisChunk005.row5501_mem, Shared.BasisChunk005.row5503_mem, Shared.BasisChunk005.row5504_mem, Shared.BasisChunk005.row5505_mem, Shared.BasisChunk005.row5506_mem, Shared.BasisChunk005.row5508_mem, Shared.BasisChunk005.row5509_mem, Shared.BasisChunk005.row5510_mem, Shared.BasisChunk005.row5511_mem, Shared.BasisChunk005.row5512_mem, Shared.BasisChunk005.row5513_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard071
