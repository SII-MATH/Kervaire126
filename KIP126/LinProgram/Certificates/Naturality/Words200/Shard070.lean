module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard070
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk005

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard070
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard070
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
  exact ⟨Shared.RelationChunk000.relation2_zero, Shared.RelationChunk000.relation15_zero, Shared.RelationChunk022.relation986_zero, Shared.RelationChunk022.relation987_zero, Shared.RelationChunk022.relation988_zero, Shared.RelationChunk022.relation989_zero, Shared.RelationChunk022.relation990_zero, Shared.RelationChunk022.relation991_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 8962 128 := by cbv
private def targetRows : List BasisRow := [⟨20, 165, 1, "703,1"⟩,
  ⟨20, 165, 2, "13,1,473,1"⟩,
  ⟨19, 165, 0, "706,1"⟩,
  ⟨19, 165, 1, "705,1"⟩,
  ⟨19, 165, 2, "2,1,656,1"⟩,
  ⟨18, 165, 0, "2,2,618,1"⟩,
  ⟨18, 165, 1, "0,1,693,1"⟩,
  ⟨18, 165, 2, "0,3,669,1"⟩,
  ⟨18, 165, 3, "0,3,17,1,367,1"⟩,
  ⟨17, 165, 0, "13,1,474,1"⟩,
  ⟨17, 165, 2, "3,1,618,1"⟩,
  ⟨17, 165, 3, "0,3,671,1"⟩,
  ⟨16, 165, 1, "13,1,476,1"⟩,
  ⟨16, 165, 2, "8,1,534,1"⟩,
  ⟨15, 165, 1, "17,1,415,1"⟩,
  ⟨15, 165, 2, "1,1,680,1"⟩,
  ⟨14, 165, 0, "710,1"⟩,
  ⟨14, 165, 1, "709,1"⟩,
  ⟨14, 165, 2, "1,1,683,1"⟩,
  ⟨13, 165, 0, "9,1,504,1"⟩,
  ⟨13, 165, 1, "1,1,21,1,324,1"⟩,
  ⟨12, 165, 0, "711,1"⟩,
  ⟨11, 165, 0, "713,1"⟩,
  ⟨11, 165, 1, "712,1"⟩,
  ⟨11, 165, 2, "0,1,18,1,366,1"⟩,
  ⟨11, 165, 3, "0,3,676,1"⟩,
  ⟨10, 165, 0, "714,1"⟩,
  ⟨10, 165, 1, "18,1,373,1"⟩,
  ⟨10, 165, 2, "0,1,18,1,367,1"⟩,
  ⟨10, 165, 3, "0,1,8,2,324,1"⟩,
  ⟨10, 165, 4, "0,1,7,1,546,1"⟩,
  ⟨10, 165, 5, "0,2,684,1"⟩,
  ⟨9, 165, 2, "0,1,696,1"⟩,
  ⟨9, 165, 3, "0,1,22,1,324,1"⟩,
  ⟨8, 165, 0, "0,1,698,1"⟩,
  ⟨8, 165, 1, "0,1,23,1,324,1"⟩,
  ⟨7, 165, 1, "0,1,699,1"⟩,
  ⟨7, 165, 2, "0,5,18,1,324,1"⟩,
  ⟨6, 165, 0, "18,1,378,1"⟩,
  ⟨6, 165, 1, "2,1,660,1"⟩,
  ⟨5, 165, 0, "26,1,324,1"⟩,
  ⟨4, 165, 0, "0,1,2,1,18,1,324,1"⟩,
  ⟨166, 166, 0, "0,166"⟩,
  ⟨55, 166, 0, "0,10,606,1"⟩,
  ⟨53, 166, 0, "0,1,700,1"⟩,
  ⟨52, 166, 0, "0,1,701,1"⟩,
  ⟨49, 166, 0, "0,7,635,1"⟩,
  ⟨48, 166, 0, "0,7,636,1"⟩,
  ⟨43, 166, 0, "0,1,16,1,402,1"⟩,
  ⟨42, 166, 0, "0,1,16,1,403,1"⟩,
  ⟨42, 166, 1, "0,2,685,1"⟩,
  ⟨41, 166, 1, "0,1,17,1,403,1"⟩,
  ⟨40, 166, 0, "0,2,686,1"⟩,
  ⟨39, 166, 0, "0,1,8,3,224,1"⟩,
  ⟨39, 166, 1, "0,38,324,1"⟩,
  ⟨38, 166, 1, "0,1,8,3,225,1"⟩,
  ⟨34, 166, 0, "1,1,5,1,64,1,137,1"⟩,
  ⟨33, 166, 0, "0,1,64,1,184,1"⟩,
  ⟨32, 166, 0, "0,1,64,1,185,1"⟩,
  ⟨32, 166, 1, "0,2,8,1,516,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk005.row5383_mem, Shared.BasisChunk005.row5384_mem, Shared.BasisChunk005.row5385_mem, Shared.BasisChunk005.row5386_mem, Shared.BasisChunk005.row5387_mem, Shared.BasisChunk005.row5388_mem, Shared.BasisChunk005.row5389_mem, Shared.BasisChunk005.row5390_mem, Shared.BasisChunk005.row5391_mem, Shared.BasisChunk005.row5392_mem, Shared.BasisChunk005.row5394_mem, Shared.BasisChunk005.row5395_mem, Shared.BasisChunk005.row5397_mem, Shared.BasisChunk005.row5398_mem, Shared.BasisChunk005.row5400_mem, Shared.BasisChunk005.row5401_mem, Shared.BasisChunk005.row5402_mem, Shared.BasisChunk005.row5403_mem, Shared.BasisChunk005.row5404_mem, Shared.BasisChunk005.row5405_mem, Shared.BasisChunk005.row5406_mem, Shared.BasisChunk005.row5407_mem, Shared.BasisChunk005.row5408_mem, Shared.BasisChunk005.row5409_mem, Shared.BasisChunk005.row5410_mem, Shared.BasisChunk005.row5411_mem, Shared.BasisChunk005.row5412_mem, Shared.BasisChunk005.row5413_mem, Shared.BasisChunk005.row5414_mem, Shared.BasisChunk005.row5415_mem, Shared.BasisChunk005.row5416_mem, Shared.BasisChunk005.row5417_mem, Shared.BasisChunk005.row5420_mem, Shared.BasisChunk005.row5421_mem, Shared.BasisChunk005.row5422_mem, Shared.BasisChunk005.row5423_mem, Shared.BasisChunk005.row5425_mem, Shared.BasisChunk005.row5426_mem, Shared.BasisChunk005.row5427_mem, Shared.BasisChunk005.row5428_mem, Shared.BasisChunk005.row5429_mem, Shared.BasisChunk005.row5430_mem, Shared.BasisChunk005.row5431_mem, Shared.BasisChunk005.row5432_mem, Shared.BasisChunk005.row5434_mem, Shared.BasisChunk005.row5435_mem, Shared.BasisChunk005.row5436_mem, Shared.BasisChunk005.row5437_mem, Shared.BasisChunk005.row5438_mem, Shared.BasisChunk005.row5439_mem, Shared.BasisChunk005.row5440_mem, Shared.BasisChunk005.row5442_mem, Shared.BasisChunk005.row5443_mem, Shared.BasisChunk005.row5444_mem, Shared.BasisChunk005.row5445_mem, Shared.BasisChunk005.row5447_mem, Shared.BasisChunk005.row5448_mem, Shared.BasisChunk005.row5449_mem, Shared.BasisChunk005.row5450_mem, Shared.BasisChunk005.row5451_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard070
