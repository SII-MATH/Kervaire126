import KIP126.LinProgram.Generated.Naturality.Words200.Shard051
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk003

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard051
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard051
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation26_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation81_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk001.relation143_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk002.relation232_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation306_zero, Shared.RelationChunk004.relation307_zero, Shared.RelationChunk004.relation308_zero, Shared.RelationChunk004.relation314_zero, Shared.RelationChunk004.relation315_zero, Shared.RelationChunk004.relation317_zero, Shared.RelationChunk004.relation321_zero, Shared.RelationChunk006.relation399_zero, Shared.RelationChunk008.relation451_zero, Shared.RelationChunk008.relation452_zero, Shared.RelationChunk008.relation453_zero, Shared.RelationChunk008.relation455_zero, Shared.RelationChunk008.relation458_zero, Shared.RelationChunk012.relation649_zero, Shared.RelationChunk013.relation677_zero, Shared.RelationChunk013.relation690_zero, Shared.RelationChunk014.relation701_zero, Shared.RelationChunk014.relation702_zero, Shared.RelationChunk014.relation703_zero, Shared.RelationChunk014.relation725_zero, Shared.RelationChunk014.relation738_zero, Shared.RelationChunk014.relation743_zero, Shared.RelationChunk014.relation745_zero, Shared.RelationChunk014.relation746_zero, Shared.RelationChunk014.relation747_zero, Shared.RelationChunk014.relation748_zero, Shared.RelationChunk014.relation749_zero, Shared.RelationChunk014.relation750_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6530 128 := by cbv
private def targetRows : List BasisRow := [⟨15, 149, 5, "0,2,8,1,333,1"⟩,
  ⟨14, 149, 0, "1,1,533,1"⟩,
  ⟨14, 149, 1, "0,1,540,1"⟩,
  ⟨14, 149, 2, "0,1,8,1,338,1"⟩,
  ⟨14, 149, 3, "0,2,534,1"⟩,
  ⟨13, 149, 0, "0,3,521,1"⟩,
  ⟨12, 149, 0, "7,1,371,1"⟩,
  ⟨12, 149, 2, "0,1,543,1"⟩,
  ⟨11, 149, 0, "1,2,513,1"⟩,
  ⟨11, 149, 1, "0,1,544,1"⟩,
  ⟨11, 149, 2, "0,1,7,1,366,1"⟩,
  ⟨11, 149, 3, "0,3,524,1"⟩,
  ⟨10, 149, 0, "69,1,133,1"⟩,
  ⟨10, 149, 1, "1,1,535,1"⟩,
  ⟨10, 149, 2, "0,1,7,1,367,1"⟩,
  ⟨10, 149, 3, "0,5,506,1"⟩,
  ⟨9, 149, 0, "69,1,134,1"⟩,
  ⟨9, 149, 1, "3,1,480,1"⟩,
  ⟨9, 149, 2, "0,1,546,1"⟩,
  ⟨8, 149, 0, "0,3,526,1"⟩,
  ⟨7, 149, 0, "0,1,2,1,506,1"⟩,
  ⟨7, 149, 1, "0,5,7,1,324,1"⟩,
  ⟨6, 149, 1, "7,1,378,1"⟩,
  ⟨5, 149, 1, "0,1,548,1"⟩,
  ⟨4, 149, 0, "0,1,2,1,7,1,324,1"⟩,
  ⟨150, 150, 0, "0,150"⟩,
  ⟨51, 150, 0, "0,2,536,1"⟩,
  ⟨47, 150, 0, "554,1"⟩,
  ⟨43, 150, 0, "8,1,16,1,183,1"⟩,
  ⟨42, 150, 0, "8,1,17,1,183,1"⟩,
  ⟨41, 150, 0, "8,1,354,1"⟩,
  ⟨40, 150, 0, "8,4,110,1"⟩,
  ⟨39, 150, 0, "8,4,111,1"⟩,
  ⟨38, 150, 1, "8,2,16,1,17,1,50,1"⟩,
  ⟨37, 150, 0, "556,1"⟩,
  ⟨37, 150, 1, "8,3,161,1"⟩,
  ⟨36, 150, 0, "8,6,31,1"⟩,
  ⟨35, 150, 0, "8,5,16,1,17,1"⟩,
  ⟨35, 150, 1, "0,4,17,1,244,1"⟩,
  ⟨34, 150, 1, "8,5,17,2"⟩,
  ⟨34, 150, 2, "0,3,17,2,138,1"⟩,
  ⟨33, 150, 0, "8,2,238,1"⟩,
  ⟨33, 150, 1, "8,5,60,1"⟩,
  ⟨33, 150, 2, "0,7,491,1"⟩,
  ⟨32, 150, 0, "8,1,17,1,185,1"⟩,
  ⟨32, 150, 1, "8,7,13,1"⟩,
  ⟨32, 150, 2, "0,5,509,1"⟩,
  ⟨31, 150, 0, "17,2,147,1"⟩,
  ⟨31, 150, 1, "8,6,32,1"⟩,
  ⟨30, 150, 0, "8,4,112,1"⟩,
  ⟨30, 150, 1, "8,5,13,1,23,1"⟩,
  ⟨29, 150, 0, "8,4,113,1"⟩,
  ⟨29, 150, 1, "8,4,13,1,51,1"⟩,
  ⟨28, 150, 1, "8,3,162,1"⟩,
  ⟨28, 150, 2, "8,3,13,4"⟩,
  ⟨27, 150, 0, "64,1,138,1"⟩,
  ⟨27, 150, 1, "8,2,23,1,113,1"⟩,
  ⟨27, 150, 2, "8,2,13,3,32,1"⟩,
  ⟨27, 150, 3, "0,1,16,1,260,1"⟩,
  ⟨26, 150, 0, "557,1"⟩,
  ⟨26, 150, 1, "8,1,13,4,23,1"⟩,
  ⟨26, 150, 2, "8,3,9,1,101,1"⟩,
  ⟨26, 150, 3, "0,1,17,1,260,1"⟩,
  ⟨25, 150, 0, "559,1"⟩,
  ⟨25, 150, 2, "13,4,51,1"⟩,
  ⟨25, 150, 3, "8,2,9,1,13,1,80,1"⟩,
  ⟨24, 150, 0, "13,4,52,1"⟩,
  ⟨24, 150, 1, "8,1,16,1,187,1"⟩,
  ⟨24, 150, 2, "8,1,9,1,23,1,101,1"⟩,
  ⟨24, 150, 3, "0,6,500,1"⟩,
  ⟨23, 150, 0, "9,1,13,1,23,1,80,1"⟩,
  ⟨23, 150, 1, "8,1,16,1,188,1"⟩,
  ⟨23, 150, 2, "0,1,8,1,346,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk003.row3921_mem, Shared.BasisChunk003.row3922_mem, Shared.BasisChunk003.row3923_mem, Shared.BasisChunk003.row3924_mem, Shared.BasisChunk003.row3925_mem, Shared.BasisChunk003.row3926_mem, Shared.BasisChunk003.row3927_mem, Shared.BasisChunk003.row3929_mem, Shared.BasisChunk003.row3930_mem, Shared.BasisChunk003.row3931_mem, Shared.BasisChunk003.row3932_mem, Shared.BasisChunk003.row3933_mem, Shared.BasisChunk003.row3934_mem, Shared.BasisChunk003.row3935_mem, Shared.BasisChunk003.row3936_mem, Shared.BasisChunk003.row3937_mem, Shared.BasisChunk003.row3938_mem, Shared.BasisChunk003.row3939_mem, Shared.BasisChunk003.row3940_mem, Shared.BasisChunk003.row3941_mem, Shared.BasisChunk003.row3942_mem, Shared.BasisChunk003.row3943_mem, Shared.BasisChunk003.row3945_mem, Shared.BasisChunk003.row3947_mem, Shared.BasisChunk003.row3948_mem, Shared.BasisChunk003.row3949_mem, Shared.BasisChunk003.row3950_mem, Shared.BasisChunk003.row3952_mem, Shared.BasisChunk003.row3954_mem, Shared.BasisChunk003.row3955_mem, Shared.BasisChunk003.row3956_mem, Shared.BasisChunk003.row3957_mem, Shared.BasisChunk003.row3958_mem, Shared.BasisChunk003.row3960_mem, Shared.BasisChunk003.row3961_mem, Shared.BasisChunk003.row3962_mem, Shared.BasisChunk003.row3963_mem, Shared.BasisChunk003.row3964_mem, Shared.BasisChunk003.row3965_mem, Shared.BasisChunk003.row3967_mem, Shared.BasisChunk003.row3968_mem, Shared.BasisChunk003.row3969_mem, Shared.BasisChunk003.row3970_mem, Shared.BasisChunk003.row3971_mem, Shared.BasisChunk003.row3972_mem, Shared.BasisChunk003.row3973_mem, Shared.BasisChunk003.row3974_mem, Shared.BasisChunk003.row3975_mem, Shared.BasisChunk003.row3976_mem, Shared.BasisChunk003.row3977_mem, Shared.BasisChunk003.row3978_mem, Shared.BasisChunk003.row3979_mem, Shared.BasisChunk003.row3980_mem, Shared.BasisChunk003.row3982_mem, Shared.BasisChunk003.row3983_mem, Shared.BasisChunk003.row3984_mem, Shared.BasisChunk003.row3985_mem, Shared.BasisChunk003.row3986_mem, Shared.BasisChunk003.row3987_mem, Shared.BasisChunk003.row3988_mem, Shared.BasisChunk003.row3989_mem, Shared.BasisChunk003.row3990_mem, Shared.BasisChunk003.row3991_mem, Shared.BasisChunk003.row3992_mem, Shared.BasisChunk003.row3994_mem, Shared.BasisChunk003.row3995_mem, Shared.BasisChunk003.row3996_mem, Shared.BasisChunk003.row3997_mem, Shared.BasisChunk003.row3998_mem, Shared.BasisChunk003.row3999_mem, Shared.BasisChunk003.row4000_mem, Shared.BasisChunk003.row4001_mem, Shared.BasisChunk003.row4002_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard051
