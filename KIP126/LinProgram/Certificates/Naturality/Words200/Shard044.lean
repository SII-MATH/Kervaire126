module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard044
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard044
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard044
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation18_zero, Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation25_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation63_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation91_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation283_zero, Shared.RelationChunk003.relation284_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk006.relation389_zero, Shared.RelationChunk006.relation390_zero, Shared.RelationChunk006.relation400_zero, Shared.RelationChunk006.relation405_zero, Shared.RelationChunk010.relation570_zero, Shared.RelationChunk011.relation593_zero, Shared.RelationChunk011.relation594_zero, Shared.RelationChunk011.relation595_zero, Shared.RelationChunk011.relation596_zero, Shared.RelationChunk011.relation597_zero, Shared.RelationChunk011.relation598_zero, Shared.RelationChunk011.relation601_zero, Shared.RelationChunk011.relation602_zero, Shared.RelationChunk011.relation603_zero, Shared.RelationChunk011.relation604_zero, Shared.RelationChunk011.relation605_zero, Shared.RelationChunk011.relation606_zero, Shared.RelationChunk011.relation610_zero, Shared.RelationChunk011.relation611_zero, Shared.RelationChunk011.relation612_zero, Shared.RelationChunk011.relation613_zero, Shared.RelationChunk011.relation614_zero, Shared.RelationChunk011.relation615_zero, Shared.RelationChunk011.relation616_zero, Shared.RelationChunk011.relation617_zero, Shared.RelationChunk012.relation634_zero, Shared.RelationChunk012.relation635_zero, Shared.RelationChunk012.relation636_zero, Shared.RelationChunk012.relation637_zero, Shared.RelationChunk012.relation638_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 5634 128 := by cbv
private def targetRows : List BasisRow := [⟨28, 143, 0, "8,2,206,1"⟩,
  ⟨27, 143, 0, "8,1,17,1,160,1"⟩,
  ⟨26, 143, 1, "8,2,207,1"⟩,
  ⟨25, 143, 0, "8,2,208,1"⟩,
  ⟨25, 143, 1, "0,2,64,1,113,1"⟩,
  ⟨24, 143, 0, "8,1,9,1,194,1"⟩,
  ⟨23, 143, 0, "9,1,13,1,167,1"⟩,
  ⟨22, 143, 1, "0,6,422,1"⟩,
  ⟨21, 143, 0, "8,1,292,1"⟩,
  ⟨21, 143, 1, "0,2,8,1,9,1,188,1"⟩,
  ⟨19, 143, 1, "0,5,440,1"⟩,
  ⟨18, 143, 0, "8,2,209,1"⟩,
  ⟨18, 143, 1, "0,4,449,1"⟩,
  ⟨17, 143, 1, "8,1,294,1"⟩,
  ⟨17, 143, 2, "1,2,448,1"⟩,
  ⟨17, 143, 3, "0,15,69,2"⟩,
  ⟨16, 143, 1, "13,1,261,1"⟩,
  ⟨16, 143, 2, "0,1,481,1"⟩,
  ⟨16, 143, 3, "0,1,69,1,112,1"⟩,
  ⟨16, 143, 4, "0,1,2,1,439,1"⟩,
  ⟨16, 143, 5, "0,15,324,1"⟩,
  ⟨15, 143, 1, "13,1,262,1"⟩,
  ⟨15, 143, 2, "0,1,482,1"⟩,
  ⟨15, 143, 3, "0,1,69,1,113,1"⟩,
  ⟨15, 143, 4, "0,2,475,1"⟩,
  ⟨14, 143, 0, "74,1,107,1"⟩,
  ⟨14, 143, 1, "9,1,281,1"⟩,
  ⟨14, 143, 2, "3,1,407,1"⟩,
  ⟨14, 143, 3, "0,1,483,1"⟩,
  ⟨13, 143, 0, "496,1"⟩,
  ⟨13, 143, 1, "76,1,107,1"⟩,
  ⟨13, 143, 2, "0,1,484,1"⟩,
  ⟨13, 143, 3, "0,1,3,1,386,1"⟩,
  ⟨12, 143, 1, "1,1,477,1"⟩,
  ⟨12, 143, 2, "0,1,486,1"⟩,
  ⟨12, 143, 3, "0,1,485,1"⟩,
  ⟨12, 143, 4, "0,1,3,1,389,1"⟩,
  ⟨12, 143, 5, "0,4,451,1"⟩,
  ⟨11, 143, 0, "7,1,311,1"⟩,
  ⟨11, 143, 2, "2,1,450,1"⟩,
  ⟨11, 143, 3, "1,1,478,1"⟩,
  ⟨11, 143, 4, "0,1,3,1,391,1"⟩,
  ⟨11, 143, 5, "0,1,3,1,390,1"⟩,
  ⟨11, 143, 6, "0,2,479,1"⟩,
  ⟨11, 143, 7, "0,5,446,1"⟩,
  ⟨10, 143, 0, "7,1,314,1"⟩,
  ⟨10, 143, 2, "0,1,3,1,392,1"⟩,
  ⟨10, 143, 3, "0,1,2,1,445,1"⟩,
  ⟨10, 143, 4, "0,2,480,1"⟩,
  ⟨9, 143, 0, "0,1,3,1,397,1"⟩,
  ⟨9, 143, 1, "0,1,3,1,396,1"⟩,
  ⟨8, 143, 0, "0,1,3,1,398,1"⟩,
  ⟨144, 144, 0, "0,144"⟩,
  ⟨47, 144, 0, "0,3,469,1"⟩,
  ⟨43, 144, 0, "8,1,296,1"⟩,
  ⟨40, 144, 0, "8,3,145,1"⟩,
  ⟨39, 144, 0, "8,2,16,1,111,1"⟩,
  ⟨38, 144, 0, "8,2,17,1,111,1"⟩,
  ⟨37, 144, 0, "8,2,211,1"⟩,
  ⟨36, 144, 0, "8,5,49,1"⟩,
  ⟨36, 144, 1, "0,4,452,1"⟩,
  ⟨35, 144, 0, "8,5,50,1"⟩,
  ⟨35, 144, 1, "0,3,17,1,225,1"⟩,
  ⟨34, 144, 1, "8,3,16,1,17,2"⟩,
  ⟨33, 144, 0, "8,1,298,1"⟩,
  ⟨33, 144, 1, "8,4,88,1"⟩,
  ⟨33, 144, 2, "0,1,488,1"⟩,
  ⟨32, 144, 0, "17,1,238,1"⟩,
  ⟨32, 144, 1, "8,8"⟩,
  ⟨31, 144, 0, "8,6,22,1"⟩,
  ⟨31, 144, 1, "0,1,489,1"⟩,
  ⟨30, 144, 0, "8,3,146,1"⟩,
  ⟨30, 144, 1, "8,6,23,1"⟩,
  ⟨29, 144, 0, "8,3,147,1"⟩,
  ⟨29, 144, 1, "8,5,51,1"⟩,
  ⟨28, 144, 0, "8,2,17,1,113,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3376_mem, Shared.BasisChunk003.row3377_mem, Shared.BasisChunk003.row3379_mem, Shared.BasisChunk003.row3380_mem, Shared.BasisChunk003.row3381_mem, Shared.BasisChunk003.row3382_mem, Shared.BasisChunk003.row3383_mem, Shared.BasisChunk003.row3385_mem, Shared.BasisChunk003.row3386_mem, Shared.BasisChunk003.row3387_mem, Shared.BasisChunk003.row3390_mem, Shared.BasisChunk003.row3391_mem, Shared.BasisChunk003.row3392_mem, Shared.BasisChunk003.row3394_mem, Shared.BasisChunk003.row3395_mem, Shared.BasisChunk003.row3396_mem, Shared.BasisChunk003.row3398_mem, Shared.BasisChunk003.row3399_mem, Shared.BasisChunk003.row3400_mem, Shared.BasisChunk003.row3401_mem, Shared.BasisChunk003.row3402_mem, Shared.BasisChunk003.row3404_mem, Shared.BasisChunk003.row3405_mem, Shared.BasisChunk003.row3406_mem, Shared.BasisChunk003.row3407_mem, Shared.BasisChunk003.row3408_mem, Shared.BasisChunk003.row3409_mem, Shared.BasisChunk003.row3410_mem, Shared.BasisChunk003.row3411_mem, Shared.BasisChunk003.row3412_mem, Shared.BasisChunk003.row3413_mem, Shared.BasisChunk003.row3414_mem, Shared.BasisChunk003.row3415_mem, Shared.BasisChunk003.row3417_mem, Shared.BasisChunk003.row3418_mem, Shared.BasisChunk003.row3419_mem, Shared.BasisChunk003.row3420_mem, Shared.BasisChunk003.row3421_mem, Shared.BasisChunk003.row3422_mem, Shared.BasisChunk003.row3424_mem, Shared.BasisChunk003.row3425_mem, Shared.BasisChunk003.row3426_mem, Shared.BasisChunk003.row3427_mem, Shared.BasisChunk003.row3428_mem, Shared.BasisChunk003.row3429_mem, Shared.BasisChunk003.row3430_mem, Shared.BasisChunk003.row3432_mem, Shared.BasisChunk003.row3433_mem, Shared.BasisChunk003.row3434_mem, Shared.BasisChunk003.row3435_mem, Shared.BasisChunk003.row3436_mem, Shared.BasisChunk003.row3437_mem, Shared.BasisChunk003.row3438_mem, Shared.BasisChunk003.row3439_mem, Shared.BasisChunk003.row3441_mem, Shared.BasisChunk003.row3443_mem, Shared.BasisChunk003.row3444_mem, Shared.BasisChunk003.row3445_mem, Shared.BasisChunk003.row3446_mem, Shared.BasisChunk003.row3447_mem, Shared.BasisChunk003.row3448_mem, Shared.BasisChunk003.row3449_mem, Shared.BasisChunk003.row3450_mem, Shared.BasisChunk003.row3452_mem, Shared.BasisChunk003.row3454_mem, Shared.BasisChunk003.row3455_mem, Shared.BasisChunk003.row3456_mem, Shared.BasisChunk003.row3457_mem, Shared.BasisChunk003.row3458_mem, Shared.BasisChunk003.row3459_mem, Shared.BasisChunk003.row3460_mem, Shared.BasisChunk003.row3461_mem, Shared.BasisChunk003.row3462_mem, Shared.BasisChunk003.row3463_mem, Shared.BasisChunk003.row3464_mem, Shared.BasisChunk003.row3465_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard044
