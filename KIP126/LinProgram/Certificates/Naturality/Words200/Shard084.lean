module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard084
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard084
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard084
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
  exact ⟨Shared.RelationChunk030.relation1272_zero, Shared.RelationChunk030.relation1273_zero, Shared.RelationChunk030.relation1274_zero, Shared.RelationChunk030.relation1277_zero, Shared.RelationChunk030.relation1278_zero, Shared.RelationChunk030.relation1279_zero, Shared.RelationChunk030.relation1280_zero, Shared.RelationChunk030.relation1281_zero, Shared.RelationChunk030.relation1282_zero, Shared.RelationChunk030.relation1283_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10754 128 := by cbv
private def targetRows : List BasisRow := [⟨53, 175, 0, "0,1,8,2,431,1"⟩,
  ⟨52, 175, 0, "0,1,8,1,16,1,296,1"⟩,
  ⟨49, 175, 0, "0,11,686,1"⟩,
  ⟨48, 175, 1, "0,47,324,1"⟩,
  ⟨47, 175, 0, "0,1,805,1"⟩,
  ⟨46, 175, 0, "0,1,806,1"⟩,
  ⟨44, 175, 0, "0,5,17,1,452,1"⟩,
  ⟨43, 175, 0, "0,1,8,2,432,1"⟩,
  ⟨43, 175, 1, "0,4,17,2,225,1"⟩,
  ⟨42, 175, 0, "0,1,8,2,433,1"⟩,
  ⟨42, 175, 1, "0,8,725,1"⟩,
  ⟨41, 175, 0, "0,1,8,1,17,1,298,1"⟩,
  ⟨41, 175, 1, "0,6,752,1"⟩,
  ⟨37, 175, 0, "0,1,64,1,224,1"⟩,
  ⟨36, 175, 0, "0,1,64,1,225,1"⟩,
  ⟨36, 175, 1, "0,2,16,1,491,1"⟩,
  ⟨35, 175, 0, "0,1,138,2"⟩,
  ⟨35, 175, 1, "0,2,17,1,491,1"⟩,
  ⟨34, 175, 0, "0,1,809,1"⟩,
  ⟨34, 175, 1, "0,1,807,1"⟩,
  ⟨33, 175, 0, "0,2,795,1"⟩,
  ⟨32, 175, 1, "0,2,8,3,260,1"⟩,
  ⟨31, 175, 0, "0,2,8,1,16,1,292,1"⟩,
  ⟨28, 175, 0, "820,1"⟩,
  ⟨27, 175, 0, "821,1"⟩,
  ⟨26, 175, 0, "0,1,810,1"⟩,
  ⟨26, 175, 1, "0,2,797,1"⟩,
  ⟨25, 175, 0, "1,1,797,1"⟩,
  ⟨25, 175, 1, "0,1,812,1"⟩,
  ⟨25, 175, 2, "0,1,811,1"⟩,
  ⟨25, 175, 3, "0,5,64,1,209,1"⟩,
  ⟨24, 175, 0, "13,3,23,1,75,1"⟩,
  ⟨24, 175, 1, "0,5,760,1"⟩,
  ⟨23, 175, 0, "13,3,23,1,76,1"⟩,
  ⟨23, 175, 1, "0,4,780,1"⟩,
  ⟨22, 175, 0, "0,1,7,1,627,1"⟩,
  ⟨22, 175, 1, "0,1,3,1,717,1"⟩,
  ⟨22, 175, 2, "0,5,762,1"⟩,
  ⟨21, 175, 0, "0,1,8,1,613,1"⟩,
  ⟨21, 175, 1, "0,5,763,1"⟩,
  ⟨20, 175, 0, "1,1,798,1"⟩,
  ⟨19, 175, 0, "822,1"⟩,
  ⟨19, 175, 1, "0,2,3,1,707,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6443_mem, Shared.BasisChunk006.row6444_mem, Shared.BasisChunk006.row6445_mem, Shared.BasisChunk006.row6447_mem, Shared.BasisChunk006.row6448_mem, Shared.BasisChunk006.row6449_mem, Shared.BasisChunk006.row6450_mem, Shared.BasisChunk006.row6451_mem, Shared.BasisChunk006.row6452_mem, Shared.BasisChunk006.row6453_mem, Shared.BasisChunk006.row6454_mem, Shared.BasisChunk006.row6455_mem, Shared.BasisChunk006.row6456_mem, Shared.BasisChunk006.row6457_mem, Shared.BasisChunk006.row6458_mem, Shared.BasisChunk006.row6459_mem, Shared.BasisChunk006.row6460_mem, Shared.BasisChunk006.row6461_mem, Shared.BasisChunk006.row6462_mem, Shared.BasisChunk006.row6463_mem, Shared.BasisChunk006.row6464_mem, Shared.BasisChunk006.row6466_mem, Shared.BasisChunk006.row6467_mem, Shared.BasisChunk006.row6468_mem, Shared.BasisChunk006.row6469_mem, Shared.BasisChunk006.row6470_mem, Shared.BasisChunk006.row6471_mem, Shared.BasisChunk006.row6472_mem, Shared.BasisChunk006.row6473_mem, Shared.BasisChunk006.row6474_mem, Shared.BasisChunk006.row6475_mem, Shared.BasisChunk006.row6476_mem, Shared.BasisChunk006.row6477_mem, Shared.BasisChunk006.row6478_mem, Shared.BasisChunk006.row6479_mem, Shared.BasisChunk006.row6480_mem, Shared.BasisChunk006.row6481_mem, Shared.BasisChunk006.row6482_mem, Shared.BasisChunk006.row6483_mem, Shared.BasisChunk006.row6484_mem, Shared.BasisChunk006.row6485_mem, Shared.BasisChunk006.row6486_mem, Shared.BasisChunk006.row6487_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard084
