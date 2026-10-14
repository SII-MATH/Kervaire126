module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard021
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard021
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard021
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
  exact ⟨Shared.RelationChunk000.relation2_zero, Shared.RelationChunk002.relation232_zero, Shared.RelationChunk004.relation301_zero, Shared.RelationChunk004.relation303_zero, Shared.RelationChunk004.relation304_zero, Shared.RelationChunk004.relation315_zero, Shared.RelationChunk004.relation317_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2690 128 := by cbv
private def targetRows : List BasisRow := [⟨32, 112, 0, "0,1,8,1,153,1"⟩,
  ⟨31, 112, 0, "0,1,17,1,117,1"⟩,
  ⟨27, 112, 0, "0,1,224,1"⟩,
  ⟨26, 112, 0, "0,1,225,1"⟩,
  ⟨23, 112, 0, "0,1,8,1,16,1,64,1"⟩,
  ⟨22, 112, 0, "0,1,8,1,17,1,64,1"⟩,
  ⟨22, 112, 1, "0,2,8,1,149,1"⟩,
  ⟨21, 112, 0, "0,1,8,1,154,1"⟩,
  ⟨16, 112, 0, "0,1,226,1"⟩,
  ⟨15, 112, 0, "13,2,67,1"⟩,
  ⟨15, 112, 1, "0,5,209,1"⟩,
  ⟨14, 112, 0, "228,1"⟩,
  ⟨14, 112, 1, "9,1,13,1,75,1"⟩,
  ⟨14, 112, 2, "0,2,3,1,188,1"⟩,
  ⟨13, 112, 1, "2,1,212,1"⟩,
  ⟨13, 112, 2, "0,2,3,1,189,1"⟩,
  ⟨12, 112, 0, "8,1,17,1,69,1"⟩,
  ⟨12, 112, 2, "0,2,221,1"⟩,
  ⟨11, 112, 0, "229,1"⟩,
  ⟨11, 112, 2, "0,3,216,1"⟩,
  ⟨10, 112, 0, "43,1,68,1"⟩,
  ⟨10, 112, 2, "1,1,3,1,190,1"⟩,
  ⟨9, 112, 0, "3,1,197,1"⟩,
  ⟨8, 112, 0, "3,1,198,1"⟩,
  ⟨7, 112, 0, "230,1"⟩,
  ⟨6, 112, 0, "231,1"⟩,
  ⟨113, 113, 0, "0,113"⟩,
  ⟨38, 113, 0, "0,1,227,1"⟩,
  ⟨35, 113, 0, "0,5,17,1,111,1"⟩,
  ⟨34, 113, 0, "0,2,8,1,152,1"⟩,
  ⟨34, 113, 1, "0,5,210,1"⟩,
  ⟨33, 113, 0, "0,2,8,1,153,1"⟩,
  ⟨28, 113, 0, "0,2,224,1"⟩,
  ⟨27, 113, 1, "0,2,225,1"⟩,
  ⟨24, 113, 0, "0,2,8,1,16,1,64,1"⟩,
  ⟨23, 113, 0, "0,2,8,1,17,1,64,1"⟩,
  ⟨20, 113, 0, "8,1,160,1"⟩,
  ⟨20, 113, 1, "1,1,42,1,64,1"⟩,
  ⟨19, 113, 0, "232,1"⟩,
  ⟨18, 113, 0, "233,1"⟩,
  ⟨17, 113, 0, "1,1,41,1,69,1"⟩,
  ⟨17, 113, 1, "0,2,226,1"⟩,
  ⟨16, 113, 0, "0,6,209,1"⟩,
  ⟨15, 113, 0, "0,3,3,1,188,1"⟩,
  ⟨14, 113, 0, "0,1,3,1,195,1"⟩,
  ⟨14, 113, 1, "0,1,2,1,212,1"⟩,
  ⟨13, 113, 0, "234,1"⟩,
  ⟨13, 113, 1, "0,1,8,1,17,1,69,1"⟩,
  ⟨13, 113, 2, "0,3,221,1"⟩,
  ⟨12, 113, 0, "0,1,43,1,67,1"⟩,
  ⟨11, 113, 0, "0,1,43,1,68,1"⟩,
  ⟨10, 113, 0, "0,1,3,1,197,1"⟩,
  ⟨9, 113, 1, "0,1,3,1,198,1"⟩,
  ⟨8, 113, 0, "0,1,230,1"⟩,
  ⟨6, 113, 0, "0,1,7,1,163,1"⟩,
  ⟨114, 114, 0, "0,114"⟩,
  ⟨39, 114, 0, "0,2,227,1"⟩,
  ⟨35, 114, 0, "0,6,210,1"⟩,
  ⟨31, 114, 0, "8,2,111,1"⟩,
  ⟨30, 114, 0, "16,1,17,1,50,1"⟩,
  ⟨29, 114, 0, "8,1,161,1"⟩,
  ⟨29, 114, 1, "0,3,224,1"⟩,
  ⟨28, 114, 0, "8,4,31,1"⟩,
  ⟨28, 114, 1, "0,3,225,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1636_mem, Shared.BasisChunk001.row1637_mem, Shared.BasisChunk001.row1638_mem, Shared.BasisChunk001.row1639_mem, Shared.BasisChunk001.row1640_mem, Shared.BasisChunk001.row1641_mem, Shared.BasisChunk001.row1642_mem, Shared.BasisChunk001.row1643_mem, Shared.BasisChunk001.row1644_mem, Shared.BasisChunk001.row1645_mem, Shared.BasisChunk001.row1646_mem, Shared.BasisChunk001.row1647_mem, Shared.BasisChunk001.row1648_mem, Shared.BasisChunk001.row1649_mem, Shared.BasisChunk001.row1651_mem, Shared.BasisChunk001.row1652_mem, Shared.BasisChunk001.row1653_mem, Shared.BasisChunk001.row1655_mem, Shared.BasisChunk001.row1656_mem, Shared.BasisChunk001.row1658_mem, Shared.BasisChunk001.row1659_mem, Shared.BasisChunk001.row1661_mem, Shared.BasisChunk001.row1662_mem, Shared.BasisChunk001.row1663_mem, Shared.BasisChunk001.row1664_mem, Shared.BasisChunk001.row1665_mem, Shared.BasisChunk001.row1667_mem, Shared.BasisChunk001.row1668_mem, Shared.BasisChunk001.row1669_mem, Shared.BasisChunk001.row1670_mem, Shared.BasisChunk001.row1671_mem, Shared.BasisChunk001.row1672_mem, Shared.BasisChunk001.row1673_mem, Shared.BasisChunk001.row1675_mem, Shared.BasisChunk001.row1676_mem, Shared.BasisChunk001.row1677_mem, Shared.BasisChunk001.row1678_mem, Shared.BasisChunk001.row1679_mem, Shared.BasisChunk001.row1680_mem, Shared.BasisChunk001.row1681_mem, Shared.BasisChunk001.row1682_mem, Shared.BasisChunk001.row1683_mem, Shared.BasisChunk001.row1684_mem, Shared.BasisChunk001.row1685_mem, Shared.BasisChunk001.row1686_mem, Shared.BasisChunk001.row1687_mem, Shared.BasisChunk001.row1688_mem, Shared.BasisChunk001.row1689_mem, Shared.BasisChunk001.row1690_mem, Shared.BasisChunk001.row1691_mem, Shared.BasisChunk001.row1692_mem, Shared.BasisChunk001.row1693_mem, Shared.BasisChunk001.row1695_mem, Shared.BasisChunk001.row1696_mem, Shared.BasisChunk001.row1697_mem, Shared.BasisChunk001.row1698_mem, Shared.BasisChunk001.row1699_mem, Shared.BasisChunk001.row1701_mem, Shared.BasisChunk001.row1703_mem, Shared.BasisChunk001.row1704_mem, Shared.BasisChunk001.row1705_mem, Shared.BasisChunk001.row1706_mem, Shared.BasisChunk001.row1707_mem, Shared.BasisChunk001.row1708_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard021
