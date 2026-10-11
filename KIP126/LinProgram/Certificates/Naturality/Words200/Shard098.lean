module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard098
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard098
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard098
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
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12546 128 := by cbv
private def targetRows : List BasisRow := [⟨12, 183, 0, "2,1,884,1"⟩,
  ⟨12, 183, 1, "0,1,43,1,397,1"⟩,
  ⟨12, 183, 2, "0,1,43,1,396,1"⟩,
  ⟨12, 183, 3, "0,1,3,1,818,1"⟩,
  ⟨11, 183, 0, "0,1,43,1,398,1"⟩,
  ⟨11, 183, 1, "0,7,849,1"⟩,
  ⟨10, 183, 1, "0,7,850,1"⟩,
  ⟨9, 183, 1, "2,1,885,1"⟩,
  ⟨9, 183, 3, "0,2,894,1"⟩,
  ⟨8, 183, 0, "53,1,324,1"⟩,
  ⟨8, 183, 1, "0,1,913,1"⟩,
  ⟨8, 183, 2, "0,2,9,1,18,1,324,1"⟩,
  ⟨7, 183, 0, "0,1,10,1,18,1,324,1"⟩,
  ⟨184, 184, 0, "0,184"⟩,
  ⟨61, 184, 0, "926,1"⟩,
  ⟨58, 184, 0, "0,4,17,1,554,1"⟩,
  ⟨57, 184, 0, "0,1,8,1,700,1"⟩,
  ⟨57, 184, 1, "0,56,324,1"⟩,
  ⟨56, 184, 0, "0,1,8,1,701,1"⟩,
  ⟨55, 184, 0, "0,1,17,1,579,1"⟩,
  ⟨51, 184, 0, "0,1,916,1"⟩,
  ⟨50, 184, 0, "0,1,917,1"⟩,
  ⟨47, 184, 0, "0,1,8,1,16,1,402,1"⟩,
  ⟨46, 184, 0, "0,1,8,1,16,1,403,1"⟩,
  ⟨46, 184, 1, "0,2,8,1,685,1"⟩,
  ⟨45, 184, 0, "0,1,8,1,17,1,403,1"⟩,
  ⟨43, 184, 0, "0,10,807,1"⟩,
  ⟨42, 184, 0, "0,11,795,1"⟩,
  ⟨40, 184, 0, "0,2,896,1"⟩,
  ⟨39, 184, 0, "0,1,918,1"⟩,
  ⟨39, 184, 1, "0,5,64,1,244,1"⟩,
  ⟨38, 184, 0, "0,5,138,1,149,1"⟩,
  ⟨37, 184, 0, "0,5,17,2,260,1"⟩,
  ⟨36, 184, 0, "0,2,8,2,516,1"⟩,
  ⟨36, 184, 1, "0,5,64,1,246,1"⟩,
  ⟨36, 184, 2, "0,5,59,1,260,1"⟩,
  ⟨35, 184, 0, "0,2,8,1,17,1,380,1"⟩,
  ⟨35, 184, 1, "0,6,862,1"⟩,
  ⟨31, 184, 0, "927,1"⟩,
  ⟨30, 184, 0, "928,1"⟩,
  ⟨30, 184, 1, "0,2,64,1,260,1"⟩,
  ⟨29, 184, 0, "64,1,274,1"⟩,
  ⟨29, 184, 1, "8,1,715,1"⟩,
  ⟨29, 184, 3, "0,2,897,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7493_mem, Shared.BasisChunk007.row7494_mem, Shared.BasisChunk007.row7495_mem, Shared.BasisChunk007.row7496_mem, Shared.BasisChunk007.row7497_mem, Shared.BasisChunk007.row7498_mem, Shared.BasisChunk007.row7500_mem, Shared.BasisChunk007.row7502_mem, Shared.BasisChunk007.row7504_mem, Shared.BasisChunk007.row7505_mem, Shared.BasisChunk007.row7506_mem, Shared.BasisChunk007.row7507_mem, Shared.BasisChunk007.row7508_mem, Shared.BasisChunk007.row7509_mem, Shared.BasisChunk007.row7511_mem, Shared.BasisChunk007.row7512_mem, Shared.BasisChunk007.row7513_mem, Shared.BasisChunk007.row7514_mem, Shared.BasisChunk007.row7515_mem, Shared.BasisChunk007.row7516_mem, Shared.BasisChunk007.row7517_mem, Shared.BasisChunk007.row7518_mem, Shared.BasisChunk007.row7519_mem, Shared.BasisChunk007.row7520_mem, Shared.BasisChunk007.row7521_mem, Shared.BasisChunk007.row7522_mem, Shared.BasisChunk007.row7523_mem, Shared.BasisChunk007.row7524_mem, Shared.BasisChunk007.row7525_mem, Shared.BasisChunk007.row7526_mem, Shared.BasisChunk007.row7527_mem, Shared.BasisChunk007.row7528_mem, Shared.BasisChunk007.row7529_mem, Shared.BasisChunk007.row7530_mem, Shared.BasisChunk007.row7531_mem, Shared.BasisChunk007.row7532_mem, Shared.BasisChunk007.row7533_mem, Shared.BasisChunk007.row7534_mem, Shared.BasisChunk007.row7536_mem, Shared.BasisChunk007.row7537_mem, Shared.BasisChunk007.row7538_mem, Shared.BasisChunk007.row7539_mem, Shared.BasisChunk007.row7540_mem, Shared.BasisChunk007.row7542_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard098
