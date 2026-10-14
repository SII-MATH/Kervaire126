module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard112
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk012
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk046
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk047
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard112
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard112
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
  exact ⟨Shared.RelationChunk000.relation22_zero, Shared.RelationChunk012.relation624_zero, Shared.RelationChunk024.relation1064_zero, Shared.RelationChunk024.relation1065_zero, Shared.RelationChunk026.relation1140_zero, Shared.RelationChunk046.relation1709_zero, Shared.RelationChunk046.relation1710_zero, Shared.RelationChunk046.relation1711_zero, Shared.RelationChunk046.relation1712_zero, Shared.RelationChunk047.relation1713_zero, Shared.RelationChunk047.relation1714_zero, Shared.RelationChunk047.relation1715_zero, Shared.RelationChunk047.relation1716_zero, Shared.RelationChunk047.relation1717_zero, Shared.RelationChunk047.relation1718_zero, Shared.RelationChunk047.relation1719_zero, Shared.RelationChunk047.relation1720_zero, Shared.RelationChunk047.relation1721_zero, Shared.RelationChunk047.relation1722_zero, Shared.RelationChunk047.relation1723_zero, Shared.RelationChunk047.relation1724_zero, Shared.RelationChunk047.relation1725_zero, Shared.RelationChunk047.relation1726_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14338 128 := by cbv
private def targetRows : List BasisRow := [⟨27, 192, 1, "8,1,813,1"⟩,
  ⟨27, 192, 3, "2,1,973,1"⟩,
  ⟨27, 192, 4, "0,1,1035,1"⟩,
  ⟨27, 192, 5, "0,1,64,1,318,1"⟩,
  ⟨26, 192, 0, "13,3,267,1"⟩,
  ⟨26, 192, 1, "9,1,13,2,286,1"⟩,
  ⟨26, 192, 2, "8,2,610,1"⟩,
  ⟨26, 192, 3, "1,2,978,1"⟩,
  ⟨25, 192, 0, "13,3,268,1"⟩,
  ⟨25, 192, 1, "8,1,80,1,201,1"⟩,
  ⟨25, 192, 2, "2,1,978,1"⟩,
  ⟨24, 192, 0, "9,1,80,1,188,1"⟩,
  ⟨24, 192, 2, "3,1,929,1"⟩,
  ⟨23, 192, 0, "1049,1"⟩,
  ⟨23, 192, 1, "13,2,23,1,213,1"⟩,
  ⟨23, 192, 3, "0,1,1036,1"⟩,
  ⟨22, 192, 0, "65,1,324,1"⟩,
  ⟨22, 192, 1, "9,1,13,2,288,1"⟩,
  ⟨22, 192, 2, "0,1,1037,1"⟩,
  ⟨21, 192, 2, "0,2,1011,1"⟩,
  ⟨20, 192, 1, "0,1,1040,1"⟩,
  ⟨20, 192, 2, "0,1,1039,1"⟩,
  ⟨20, 192, 3, "0,2,1014,1"⟩,
  ⟨20, 192, 4, "0,4,987,1"⟩,
  ⟨19, 192, 1, "1,1,1014,1"⟩,
  ⟨19, 192, 2, "1,1,1013,1"⟩,
  ⟨19, 192, 3, "0,2,1015,1"⟩,
  ⟨19, 192, 4, "0,4,17,2,324,1"⟩,
  ⟨18, 192, 1, "0,1,8,1,39,1,324,1"⟩,
  ⟨18, 192, 2, "0,2,1017,1"⟩,
  ⟨18, 192, 3, "0,4,59,1,324,1"⟩,
  ⟨17, 192, 0, "1,1,1019,1"⟩,
  ⟨17, 192, 1, "0,1,1046,1"⟩,
  ⟨17, 192, 2, "0,1,8,1,40,1,324,1"⟩,
  ⟨17, 192, 3, "0,2,1021,1"⟩,
  ⟨16, 192, 0, "1054,1"⟩,
  ⟨16, 192, 1, "3,2,843,1"⟩,
  ⟨16, 192, 2, "1,1,1022,1"⟩,
  ⟨16, 192, 3, "1,1,43,1,485,1"⟩,
  ⟨16, 192, 4, "0,1,17,1,20,1,324,1"⟩,
  ⟨15, 192, 0, "2,1,991,1"⟩,
  ⟨15, 192, 1, "2,1,990,1"⟩,
  ⟨15, 192, 2, "1,1,1023,1"⟩,
  ⟨13, 192, 1, "1,1,1026,1"⟩,
  ⟨13, 192, 2, "0,2,1027,1"⟩,
  ⟨12, 192, 0, "1,1,1027,1"⟩,
  ⟨12, 192, 1, "0,1,64,1,324,1"⟩,
  ⟨12, 192, 2, "0,2,1028,1"⟩,
  ⟨11, 192, 0, "66,1,324,1"⟩,
  ⟨11, 192, 1, "0,2,17,1,18,1,324,1"⟩,
  ⟨9, 192, 0, "2,1,18,1,617,1"⟩,
  ⟨8, 192, 1, "2,1,994,1"⟩,
  ⟨7, 192, 0, "68,1,324,1"⟩,
  ⟨193, 193, 0, "0,193"⟩,
  ⟨64, 193, 0, "1,1,1029,1"⟩,
  ⟨61, 193, 0, "0,1,8,1,803,1"⟩,
  ⟨60, 193, 0, "0,1,8,1,804,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8535_mem, Shared.BasisChunk008.row8537_mem, Shared.BasisChunk008.row8538_mem, Shared.BasisChunk008.row8539_mem, Shared.BasisChunk008.row8540_mem, Shared.BasisChunk008.row8541_mem, Shared.BasisChunk008.row8542_mem, Shared.BasisChunk008.row8543_mem, Shared.BasisChunk008.row8544_mem, Shared.BasisChunk008.row8545_mem, Shared.BasisChunk008.row8546_mem, Shared.BasisChunk008.row8547_mem, Shared.BasisChunk008.row8549_mem, Shared.BasisChunk008.row8550_mem, Shared.BasisChunk008.row8551_mem, Shared.BasisChunk008.row8553_mem, Shared.BasisChunk008.row8554_mem, Shared.BasisChunk008.row8555_mem, Shared.BasisChunk008.row8556_mem, Shared.BasisChunk008.row8559_mem, Shared.BasisChunk008.row8561_mem, Shared.BasisChunk008.row8562_mem, Shared.BasisChunk008.row8563_mem, Shared.BasisChunk008.row8564_mem, Shared.BasisChunk008.row8566_mem, Shared.BasisChunk008.row8567_mem, Shared.BasisChunk008.row8568_mem, Shared.BasisChunk008.row8569_mem, Shared.BasisChunk008.row8571_mem, Shared.BasisChunk008.row8572_mem, Shared.BasisChunk008.row8573_mem, Shared.BasisChunk008.row8574_mem, Shared.BasisChunk008.row8575_mem, Shared.BasisChunk008.row8576_mem, Shared.BasisChunk008.row8577_mem, Shared.BasisChunk008.row8578_mem, Shared.BasisChunk008.row8579_mem, Shared.BasisChunk008.row8580_mem, Shared.BasisChunk008.row8581_mem, Shared.BasisChunk008.row8582_mem, Shared.BasisChunk008.row8583_mem, Shared.BasisChunk008.row8584_mem, Shared.BasisChunk008.row8585_mem, Shared.BasisChunk008.row8589_mem, Shared.BasisChunk008.row8590_mem, Shared.BasisChunk008.row8591_mem, Shared.BasisChunk008.row8592_mem, Shared.BasisChunk008.row8593_mem, Shared.BasisChunk008.row8594_mem, Shared.BasisChunk008.row8595_mem, Shared.BasisChunk008.row8596_mem, Shared.BasisChunk008.row8598_mem, Shared.BasisChunk008.row8599_mem, Shared.BasisChunk008.row8602_mem, Shared.BasisChunk008.row8603_mem, Shared.BasisChunk008.row8604_mem, Shared.BasisChunk008.row8605_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard112
