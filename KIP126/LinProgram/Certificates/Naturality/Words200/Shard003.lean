module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk000

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard003
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard003
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
  exact ⟨Shared.RelationChunk000.relation59_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 386 128 := by cbv
private def targetRows : List BasisRow := [⟨10, 47, 0, "0,5,34,1"⟩,
  ⟨9, 47, 0, "0,3,36,1"⟩,
  ⟨48, 48, 0, "0,48"⟩,
  ⟨15, 48, 0, "0,3,39,1"⟩,
  ⟨11, 48, 0, "8,1,17,1"⟩,
  ⟨8, 48, 0, "13,2"⟩,
  ⟨6, 48, 0, "6,1,18,1"⟩,
  ⟨3, 48, 0, "3,2,18,1"⟩,
  ⟨49, 49, 0, "0,49"⟩,
  ⟨16, 49, 0, "1,1,41,1"⟩,
  ⟨13, 49, 0, "0,1,8,1,16,1"⟩,
  ⟨12, 49, 0, "0,1,8,1,17,1"⟩,
  ⟨7, 49, 0, "0,1,6,1,18,1"⟩,
  ⟨5, 49, 0, "0,1,43,1"⟩,
  ⟨4, 49, 0, "0,1,3,2,18,1"⟩,
  ⟨50, 50, 0, "0,50"⟩,
  ⟨14, 50, 0, "0,2,8,1,16,1"⟩,
  ⟨13, 50, 0, "0,2,8,1,17,1"⟩,
  ⟨8, 50, 0, "0,2,6,1,18,1"⟩,
  ⟨6, 50, 0, "0,2,43,1"⟩,
  ⟨5, 50, 1, "1,1,43,1"⟩,
  ⟨51, 51, 0, "0,51"⟩,
  ⟨11, 51, 0, "8,1,20,1"⟩,
  ⟨10, 51, 0, "45,1"⟩,
  ⟨9, 51, 0, "46,1"⟩,
  ⟨6, 51, 0, "0,1,8,1,18,1"⟩,
  ⟨52, 52, 0, "0,52"⟩,
  ⟨17, 52, 0, "47,1"⟩,
  ⟨13, 52, 0, "0,1,8,1,19,1"⟩,
  ⟨12, 52, 0, "0,1,8,1,20,1"⟩,
  ⟨11, 52, 0, "0,1,45,1"⟩,
  ⟨7, 52, 0, "0,2,8,1,18,1"⟩,
  ⟨5, 52, 0, "2,1,43,1"⟩,
  ⟨4, 52, 0, "3,1,38,1"⟩,
  ⟨53, 53, 0, "0,53"⟩,
  ⟨18, 53, 0, "0,1,47,1"⟩,
  ⟨14, 53, 0, "0,2,8,1,19,1"⟩,
  ⟨13, 53, 0, "0,2,8,1,20,1"⟩,
  ⟨6, 53, 0, "0,1,2,1,43,1"⟩,
  ⟨54, 54, 0, "0,54"⟩,
  ⟨19, 54, 0, "0,2,47,1"⟩,
  ⟨15, 54, 0, "50,1"⟩,
  ⟨11, 54, 0, "8,1,22,1"⟩,
  ⟨10, 54, 0, "8,1,23,1"⟩,
  ⟨9, 54, 0, "51,1"⟩,
  ⟨8, 54, 0, "52,1"⟩,
  ⟨7, 54, 0, "1,2,8,1,18,1"⟩,
  ⟨6, 54, 0, "0,1,9,1,18,1"⟩,
  ⟨5, 54, 0, "10,1,18,1"⟩,
  ⟨4, 54, 0, "11,1,18,1"⟩,
  ⟨55, 55, 0, "0,55"⟩,
  ⟨17, 55, 0, "0,1,49,1"⟩,
  ⟨16, 55, 0, "0,1,50,1"⟩,
  ⟨13, 55, 0, "0,1,8,3"⟩,
  ⟨12, 55, 0, "0,1,8,1,22,1"⟩,
  ⟨7, 55, 0, "53,1"⟩,
  ⟨7, 55, 1, "0,2,9,1,18,1"⟩,
  ⟨6, 55, 0, "0,1,10,1,18,1"⟩,
  ⟨56, 56, 0, "0,56"⟩,
  ⟨18, 56, 0, "0,2,49,1"⟩,
  ⟨17, 56, 1, "0,2,50,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk000.row238_mem, Shared.BasisChunk000.row239_mem, Shared.BasisChunk000.row240_mem, Shared.BasisChunk000.row241_mem, Shared.BasisChunk000.row243_mem, Shared.BasisChunk000.row245_mem, Shared.BasisChunk000.row247_mem, Shared.BasisChunk000.row249_mem, Shared.BasisChunk000.row250_mem, Shared.BasisChunk000.row251_mem, Shared.BasisChunk000.row252_mem, Shared.BasisChunk000.row253_mem, Shared.BasisChunk000.row254_mem, Shared.BasisChunk000.row255_mem, Shared.BasisChunk000.row256_mem, Shared.BasisChunk000.row257_mem, Shared.BasisChunk000.row259_mem, Shared.BasisChunk000.row260_mem, Shared.BasisChunk000.row262_mem, Shared.BasisChunk000.row263_mem, Shared.BasisChunk000.row265_mem, Shared.BasisChunk000.row266_mem, Shared.BasisChunk000.row268_mem, Shared.BasisChunk000.row269_mem, Shared.BasisChunk000.row270_mem, Shared.BasisChunk000.row271_mem, Shared.BasisChunk000.row272_mem, Shared.BasisChunk000.row274_mem, Shared.BasisChunk000.row275_mem, Shared.BasisChunk000.row276_mem, Shared.BasisChunk000.row277_mem, Shared.BasisChunk000.row278_mem, Shared.BasisChunk000.row280_mem, Shared.BasisChunk000.row281_mem, Shared.BasisChunk000.row282_mem, Shared.BasisChunk000.row283_mem, Shared.BasisChunk000.row284_mem, Shared.BasisChunk000.row285_mem, Shared.BasisChunk000.row287_mem, Shared.BasisChunk000.row289_mem, Shared.BasisChunk000.row290_mem, Shared.BasisChunk000.row292_mem, Shared.BasisChunk000.row294_mem, Shared.BasisChunk000.row295_mem, Shared.BasisChunk000.row296_mem, Shared.BasisChunk000.row297_mem, Shared.BasisChunk000.row298_mem, Shared.BasisChunk000.row299_mem, Shared.BasisChunk000.row300_mem, Shared.BasisChunk000.row301_mem, Shared.BasisChunk000.row302_mem, Shared.BasisChunk000.row303_mem, Shared.BasisChunk000.row304_mem, Shared.BasisChunk000.row305_mem, Shared.BasisChunk000.row306_mem, Shared.BasisChunk000.row309_mem, Shared.BasisChunk000.row310_mem, Shared.BasisChunk000.row311_mem, Shared.BasisChunk000.row312_mem, Shared.BasisChunk000.row313_mem, Shared.BasisChunk000.row315_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard003
