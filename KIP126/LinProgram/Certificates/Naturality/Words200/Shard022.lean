module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard022
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard022
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard022
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
  exact ⟨Shared.RelationChunk000.relation6_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation11_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation148_zero, Shared.RelationChunk001.relation193_zero, Shared.RelationChunk001.relation194_zero, Shared.RelationChunk001.relation195_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk001.relation197_zero, Shared.RelationChunk001.relation198_zero, Shared.RelationChunk002.relation226_zero, Shared.RelationChunk002.relation227_zero, Shared.RelationChunk004.relation300_zero, Shared.RelationChunk004.relation305_zero, Shared.RelationChunk004.relation306_zero, Shared.RelationChunk004.relation307_zero, Shared.RelationChunk004.relation308_zero, Shared.RelationChunk004.relation313_zero, Shared.RelationChunk004.relation318_zero, Shared.RelationChunk004.relation319_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 2818 128 := by cbv
private def targetRows : List BasisRow := [⟨27, 114, 0, "8,3,16,1,17,1"⟩,
  ⟨26, 114, 1, "8,3,17,2"⟩,
  ⟨25, 114, 0, "238,1"⟩,
  ⟨25, 114, 1, "8,3,60,1"⟩,
  ⟨24, 114, 0, "8,5,13,1"⟩,
  ⟨23, 114, 0, "8,4,32,1"⟩,
  ⟨22, 114, 1, "8,3,13,1,23,1"⟩,
  ⟨21, 114, 0, "8,2,113,1"⟩,
  ⟨21, 114, 1, "8,2,13,1,51,1"⟩,
  ⟨20, 114, 0, "8,1,162,1"⟩,
  ⟨20, 114, 1, "8,1,13,4"⟩,
  ⟨19, 114, 0, "23,1,113,1"⟩,
  ⟨19, 114, 1, "13,3,32,1"⟩,
  ⟨18, 114, 0, "13,3,33,1"⟩,
  ⟨18, 114, 1, "8,1,9,1,101,1"⟩,
  ⟨17, 114, 0, "9,1,13,1,80,1"⟩,
  ⟨15, 114, 0, "0,2,3,1,195,1"⟩,
  ⟨14, 114, 0, "0,2,8,1,17,1,69,1"⟩,
  ⟨13, 114, 0, "0,2,43,1,67,1"⟩,
  ⟨12, 114, 0, "0,2,43,1,68,1"⟩,
  ⟨10, 114, 0, "0,1,235,1"⟩,
  ⟨8, 114, 0, "3,1,203,1"⟩,
  ⟨7, 114, 0, "240,1"⟩,
  ⟨7, 114, 1, "0,2,7,1,163,1"⟩,
  ⟨6, 114, 0, "241,1"⟩,
  ⟨6, 114, 1, "1,1,7,1,163,1"⟩,
  ⟨5, 114, 0, "242,1"⟩,
  ⟨115, 115, 0, "0,115"⟩,
  ⟨37, 115, 0, "0,1,236,1"⟩,
  ⟨36, 115, 0, "0,7,210,1"⟩,
  ⟨33, 115, 0, "0,1,8,2,110,1"⟩,
  ⟨32, 115, 0, "0,1,8,2,111,1"⟩,
  ⟨30, 115, 0, "0,4,224,1"⟩,
  ⟨29, 115, 0, "0,4,225,1"⟩,
  ⟨27, 115, 0, "0,1,237,1"⟩,
  ⟨26, 115, 0, "0,1,238,1"⟩,
  ⟨23, 115, 0, "0,1,8,2,112,1"⟩,
  ⟨22, 115, 0, "0,1,8,2,113,1"⟩,
  ⟨21, 115, 0, "0,1,8,1,162,1"⟩,
  ⟨16, 115, 0, "2,1,226,1"⟩,
  ⟨14, 115, 0, "13,2,75,1"⟩,
  ⟨13, 115, 0, "13,2,76,1"⟩,
  ⟨12, 115, 1, "8,1,20,1,69,1"⟩,
  ⟨11, 115, 0, "3,1,209,1"⟩,
  ⟨11, 115, 1, "0,2,235,1"⟩,
  ⟨10, 115, 0, "43,1,74,1"⟩,
  ⟨10, 115, 1, "3,2,174,1"⟩,
  ⟨10, 115, 2, "0,1,239,1"⟩,
  ⟨9, 115, 0, "43,1,76,1"⟩,
  ⟨9, 115, 1, "0,1,3,1,203,1"⟩,
  ⟨8, 115, 0, "0,1,240,1"⟩,
  ⟨7, 115, 0, "0,1,241,1"⟩,
  ⟨116, 116, 0, "0,116"⟩,
  ⟨38, 116, 0, "0,2,236,1"⟩,
  ⟨37, 116, 1, "0,8,210,1"⟩,
  ⟨34, 116, 0, "0,2,8,2,110,1"⟩,
  ⟨33, 116, 0, "0,2,8,2,111,1"⟩,
  ⟨31, 116, 0, "0,5,224,1"⟩,
  ⟨30, 116, 0, "0,5,225,1"⟩,
  ⟨28, 116, 0, "0,2,237,1"⟩,
  ⟨27, 116, 0, "0,2,238,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1709_mem, Shared.BasisChunk001.row1711_mem, Shared.BasisChunk001.row1712_mem, Shared.BasisChunk001.row1713_mem, Shared.BasisChunk001.row1714_mem, Shared.BasisChunk001.row1715_mem, Shared.BasisChunk001.row1717_mem, Shared.BasisChunk001.row1718_mem, Shared.BasisChunk001.row1719_mem, Shared.BasisChunk001.row1720_mem, Shared.BasisChunk001.row1721_mem, Shared.BasisChunk001.row1722_mem, Shared.BasisChunk001.row1723_mem, Shared.BasisChunk001.row1724_mem, Shared.BasisChunk001.row1725_mem, Shared.BasisChunk001.row1726_mem, Shared.BasisChunk001.row1727_mem, Shared.BasisChunk001.row1728_mem, Shared.BasisChunk001.row1729_mem, Shared.BasisChunk001.row1730_mem, Shared.BasisChunk001.row1732_mem, Shared.BasisChunk001.row1734_mem, Shared.BasisChunk001.row1735_mem, Shared.BasisChunk001.row1736_mem, Shared.BasisChunk001.row1737_mem, Shared.BasisChunk001.row1738_mem, Shared.BasisChunk001.row1739_mem, Shared.BasisChunk001.row1740_mem, Shared.BasisChunk001.row1741_mem, Shared.BasisChunk001.row1742_mem, Shared.BasisChunk001.row1743_mem, Shared.BasisChunk001.row1744_mem, Shared.BasisChunk001.row1745_mem, Shared.BasisChunk001.row1746_mem, Shared.BasisChunk001.row1748_mem, Shared.BasisChunk001.row1749_mem, Shared.BasisChunk001.row1750_mem, Shared.BasisChunk001.row1751_mem, Shared.BasisChunk001.row1752_mem, Shared.BasisChunk001.row1753_mem, Shared.BasisChunk001.row1754_mem, Shared.BasisChunk001.row1755_mem, Shared.BasisChunk001.row1758_mem, Shared.BasisChunk001.row1759_mem, Shared.BasisChunk001.row1760_mem, Shared.BasisChunk001.row1761_mem, Shared.BasisChunk001.row1762_mem, Shared.BasisChunk001.row1763_mem, Shared.BasisChunk001.row1764_mem, Shared.BasisChunk001.row1765_mem, Shared.BasisChunk001.row1766_mem, Shared.BasisChunk001.row1767_mem, Shared.BasisChunk001.row1768_mem, Shared.BasisChunk001.row1769_mem, Shared.BasisChunk001.row1771_mem, Shared.BasisChunk001.row1772_mem, Shared.BasisChunk001.row1773_mem, Shared.BasisChunk001.row1774_mem, Shared.BasisChunk001.row1775_mem, Shared.BasisChunk001.row1776_mem, Shared.BasisChunk001.row1777_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard022
