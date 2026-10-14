module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard039
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard039
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard039
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
  exact ⟨Shared.RelationChunk009.relation501_zero, Shared.RelationChunk009.relation521_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 4994 128 := by cbv
private def targetRows : List BasisRow := [⟨18, 138, 2, "0,1,17,1,209,1"⟩,
  ⟨17, 138, 1, "23,1,188,1"⟩,
  ⟨17, 138, 2, "0,1,422,1"⟩,
  ⟨17, 138, 3, "0,2,7,1,267,1"⟩,
  ⟨16, 138, 1, "23,1,189,1"⟩,
  ⟨16, 138, 2, "0,1,424,1"⟩,
  ⟨15, 138, 1, "7,1,279,1"⟩,
  ⟨15, 138, 2, "0,2,418,1"⟩,
  ⟨14, 138, 0, "440,1"⟩,
  ⟨14, 138, 2, "23,1,190,1"⟩,
  ⟨14, 138, 3, "1,1,418,1"⟩,
  ⟨13, 138, 0, "24,1,190,1"⟩,
  ⟨13, 138, 2, "0,1,425,1"⟩,
  ⟨13, 138, 3, "0,4,391,1"⟩,
  ⟨13, 138, 4, "0,5,375,1"⟩,
  ⟨12, 138, 1, "3,1,336,1"⟩,
  ⟨12, 138, 2, "0,1,427,1"⟩,
  ⟨12, 138, 3, "0,2,419,1"⟩,
  ⟨12, 138, 4, "0,10,69,2"⟩,
  ⟨11, 138, 0, "0,1,428,1"⟩,
  ⟨11, 138, 1, "0,1,3,1,333,1"⟩,
  ⟨11, 138, 2, "0,1,2,1,373,1"⟩,
  ⟨11, 138, 3, "0,10,324,1"⟩,
  ⟨10, 138, 1, "441,1"⟩,
  ⟨10, 138, 2, "2,1,69,1,82,1"⟩,
  ⟨10, 138, 3, "0,2,3,1,68,1,69,1"⟩,
  ⟨9, 138, 0, "444,1"⟩,
  ⟨9, 138, 2, "0,1,429,1"⟩,
  ⟨9, 138, 3, "0,1,69,1,95,1"⟩,
  ⟨8, 138, 1, "2,1,396,1"⟩,
  ⟨7, 138, 1, "2,1,398,1"⟩,
  ⟨6, 138, 1, "3,1,340,1"⟩,
  ⟨6, 138, 2, "2,1,400,1"⟩,
  ⟨5, 138, 0, "3,1,341,1"⟩,
  ⟨5, 138, 1, "0,2,3,1,69,2"⟩,
  ⟨4, 138, 1, "0,2,3,1,324,1"⟩,
  ⟨139, 139, 0, "0,139"⟩,
  ⟨45, 139, 0, "0,1,431,1"⟩,
  ⟨44, 139, 0, "0,23,246,1"⟩,
  ⟨41, 139, 0, "0,1,8,2,182,1"⟩,
  ⟨40, 139, 0, "0,1,8,2,183,1"⟩,
  ⟨38, 139, 0, "0,4,402,1"⟩,
  ⟨37, 139, 0, "0,4,403,1"⟩,
  ⟨35, 139, 0, "0,1,432,1"⟩,
  ⟨34, 139, 0, "0,1,433,1"⟩,
  ⟨31, 139, 0, "0,1,8,2,184,1"⟩,
  ⟨30, 139, 0, "0,1,8,2,185,1"⟩,
  ⟨30, 139, 1, "0,13,300,1"⟩,
  ⟨29, 139, 0, "0,1,8,1,17,1,147,1"⟩,
  ⟨29, 139, 1, "0,11,317,1"⟩,
  ⟨24, 139, 0, "0,2,8,1,260,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2992_mem, Shared.BasisChunk002.row2994_mem, Shared.BasisChunk002.row2995_mem, Shared.BasisChunk002.row2996_mem, Shared.BasisChunk002.row2998_mem, Shared.BasisChunk002.row2999_mem, Shared.BasisChunk002.row3001_mem, Shared.BasisChunk002.row3002_mem, Shared.BasisChunk002.row3003_mem, Shared.BasisChunk002.row3005_mem, Shared.BasisChunk002.row3006_mem, Shared.BasisChunk002.row3008_mem, Shared.BasisChunk002.row3010_mem, Shared.BasisChunk002.row3011_mem, Shared.BasisChunk002.row3012_mem, Shared.BasisChunk002.row3014_mem, Shared.BasisChunk002.row3015_mem, Shared.BasisChunk002.row3016_mem, Shared.BasisChunk002.row3017_mem, Shared.BasisChunk002.row3018_mem, Shared.BasisChunk002.row3019_mem, Shared.BasisChunk002.row3020_mem, Shared.BasisChunk002.row3021_mem, Shared.BasisChunk002.row3023_mem, Shared.BasisChunk002.row3024_mem, Shared.BasisChunk002.row3025_mem, Shared.BasisChunk002.row3026_mem, Shared.BasisChunk002.row3028_mem, Shared.BasisChunk002.row3029_mem, Shared.BasisChunk002.row3031_mem, Shared.BasisChunk002.row3033_mem, Shared.BasisChunk002.row3035_mem, Shared.BasisChunk002.row3036_mem, Shared.BasisChunk002.row3037_mem, Shared.BasisChunk002.row3038_mem, Shared.BasisChunk002.row3040_mem, Shared.BasisChunk002.row3042_mem, Shared.BasisChunk002.row3043_mem, Shared.BasisChunk002.row3044_mem, Shared.BasisChunk002.row3045_mem, Shared.BasisChunk002.row3046_mem, Shared.BasisChunk002.row3047_mem, Shared.BasisChunk002.row3048_mem, Shared.BasisChunk002.row3050_mem, Shared.BasisChunk002.row3051_mem, Shared.BasisChunk002.row3052_mem, Shared.BasisChunk002.row3053_mem, Shared.BasisChunk002.row3054_mem, Shared.BasisChunk002.row3055_mem, Shared.BasisChunk002.row3056_mem, Shared.BasisChunk002.row3057_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard039
