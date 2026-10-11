module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard114
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk010
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk018
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk048
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk050
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard114
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard114
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
  exact ⟨Shared.RelationChunk000.relation8_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk002.relation223_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk008.relation449_zero, Shared.RelationChunk010.relation553_zero, Shared.RelationChunk010.relation554_zero, Shared.RelationChunk010.relation555_zero, Shared.RelationChunk010.relation556_zero, Shared.RelationChunk010.relation557_zero, Shared.RelationChunk010.relation558_zero, Shared.RelationChunk010.relation559_zero, Shared.RelationChunk010.relation560_zero, Shared.RelationChunk010.relation561_zero, Shared.RelationChunk013.relation675_zero, Shared.RelationChunk018.relation877_zero, Shared.RelationChunk018.relation879_zero, Shared.RelationChunk031.relation1313_zero, Shared.RelationChunk048.relation1755_zero, Shared.RelationChunk048.relation1756_zero, Shared.RelationChunk048.relation1757_zero, Shared.RelationChunk048.relation1758_zero, Shared.RelationChunk048.relation1759_zero, Shared.RelationChunk048.relation1760_zero, Shared.RelationChunk048.relation1761_zero, Shared.RelationChunk050.relation1776_zero, Shared.RelationChunk050.relation1777_zero, Shared.RelationChunk050.relation1778_zero, Shared.RelationChunk050.relation1779_zero, Shared.RelationChunk050.relation1780_zero, Shared.RelationChunk050.relation1781_zero, Shared.RelationChunk050.relation1782_zero, Shared.RelationChunk050.relation1783_zero, Shared.RelationChunk050.relation1784_zero, Shared.RelationChunk050.relation1785_zero, Shared.RelationChunk050.relation1786_zero, Shared.RelationChunk050.relation1787_zero, Shared.RelationChunk050.relation1789_zero, Shared.RelationChunk050.relation1790_zero, Shared.RelationChunk050.relation1791_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 14594 128 := by cbv
private def targetRows : List BasisRow := [⟨23, 193, 0, "1063,1"⟩,
  ⟨23, 193, 1, "1062,1"⟩,
  ⟨23, 193, 2, "0,1,65,1,324,1"⟩,
  ⟨22, 193, 0, "23,1,618,1"⟩,
  ⟨22, 193, 1, "0,1,1051,1"⟩,
  ⟨22, 193, 2, "0,3,1011,1"⟩,
  ⟨21, 193, 0, "76,1,302,1"⟩,
  ⟨21, 193, 1, "18,1,655,1"⟩,
  ⟨21, 193, 2, "13,1,75,1,188,1"⟩,
  ⟨20, 193, 2, "13,1,75,1,189,1"⟩,
  ⟨20, 193, 3, "0,3,1015,1"⟩,
  ⟨20, 193, 4, "0,5,17,2,324,1"⟩,
  ⟨19, 193, 1, "13,1,23,1,373,1"⟩,
  ⟨19, 193, 2, "1,1,1043,1"⟩,
  ⟨19, 193, 3, "1,1,1042,1"⟩,
  ⟨19, 193, 4, "0,2,8,1,39,1,324,1"⟩,
  ⟨19, 193, 5, "0,5,59,1,324,1"⟩,
  ⟨18, 193, 1, "1067,1"⟩,
  ⟨18, 193, 2, "13,1,75,1,190,1"⟩,
  ⟨18, 193, 3, "13,1,23,1,376,1"⟩,
  ⟨18, 193, 4, "2,1,1002,1"⟩,
  ⟨18, 193, 5, "0,2,8,1,40,1,324,1"⟩,
  ⟨17, 193, 0, "9,1,787,1"⟩,
  ⟨17, 193, 1, "2,1,1004,1"⟩,
  ⟨16, 193, 1, "1069,1"⟩,
  ⟨16, 193, 2, "67,1,333,1"⟩,
  ⟨15, 193, 1, "1071,1"⟩,
  ⟨15, 193, 2, "1,1,1047,1"⟩,
  ⟨15, 193, 3, "0,1,1056,1"⟩,
  ⟨15, 193, 4, "0,1,1055,1"⟩,
  ⟨14, 193, 0, "1073,1"⟩,
  ⟨14, 193, 1, "2,1,1008,1"⟩,
  ⟨14, 193, 2, "0,1,1057,1"⟩,
  ⟨13, 193, 0, "7,1,860,1"⟩,
  ⟨13, 193, 1, "0,2,64,1,324,1"⟩,
  ⟨12, 193, 0, "1074,1"⟩,
  ⟨12, 193, 2, "0,1,66,1,324,1"⟩,
  ⟨11, 193, 0, "70,1,323,1"⟩,
  ⟨11, 193, 1, "18,2,333,1"⟩,
  ⟨10, 193, 0, "18,1,659,1"⟩,
  ⟨9, 193, 0, "18,1,20,1,324,1"⟩,
  ⟨9, 193, 1, "0,1,67,1,324,1"⟩,
  ⟨8, 193, 0, "0,1,68,1,324,1"⟩,
  ⟨5, 193, 1, "0,1,1058,1"⟩,
  ⟨4, 193, 0, "0,1,18,2,324,1"⟩,
  ⟨194, 194, 0, "0,194"⟩,
  ⟨62, 194, 0, "0,2,8,1,803,1"⟩,
  ⟨61, 194, 0, "0,2,8,1,804,1"⟩,
  ⟨54, 194, 0, "0,6,969,1"⟩,
  ⟨53, 194, 0, "0,5,17,1,636,1"⟩,
  ⟨52, 194, 0, "0,2,8,1,805,1"⟩,
  ⟨51, 194, 0, "0,2,8,1,806,1"⟩,
  ⟨51, 194, 1, "0,3,1030,1"⟩,
  ⟨47, 194, 0, "17,1,685,1"⟩,
  ⟨46, 194, 0, "16,1,686,1"⟩,
  ⟨45, 194, 0, "8,1,829,1"⟩,
  ⟨45, 194, 1, "0,3,1033,1"⟩,
  ⟨44, 194, 0, "8,3,452,1"⟩,
  ⟨44, 194, 1, "0,1,1059,1"⟩,
  ⟨43, 194, 0, "8,1,16,1,17,1,244,1"⟩,
  ⟨42, 194, 1, "8,2,31,1,245,1"⟩,
  ⟨41, 194, 0, "8,3,453,1"⟩,
  ⟨41, 194, 1, "0,2,8,1,64,1,225,1"⟩,
  ⟨40, 194, 0, "8,4,16,1,149,1"⟩,
  ⟨39, 194, 0, "8,4,17,1,149,1"⟩,
  ⟨38, 194, 2, "8,4,277,1"⟩,
  ⟨38, 194, 3, "0,11,919,1"⟩,
  ⟨37, 194, 0, "113,1,244,1"⟩,
  ⟨37, 194, 1, "8,1,17,1,516,1"⟩,
  ⟨37, 194, 2, "8,5,193,1"⟩,
  ⟨37, 194, 3, "0,12,898,1"⟩,
  ⟨36, 194, 0, "17,2,380,1"⟩,
  ⟨36, 194, 1, "8,1,830,1"⟩,
  ⟨36, 194, 2, "8,5,194,1"⟩,
  ⟨35, 194, 0, "42,1,516,1"⟩,
  ⟨35, 194, 1, "8,1,831,1"⟩,
  ⟨35, 194, 2, "8,4,13,1,167,1"⟩,
  ⟨35, 194, 3, "0,1,1060,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8644_mem, Shared.BasisChunk008.row8645_mem, Shared.BasisChunk008.row8646_mem, Shared.BasisChunk008.row8647_mem, Shared.BasisChunk008.row8648_mem, Shared.BasisChunk008.row8649_mem, Shared.BasisChunk008.row8650_mem, Shared.BasisChunk008.row8651_mem, Shared.BasisChunk008.row8652_mem, Shared.BasisChunk008.row8656_mem, Shared.BasisChunk008.row8657_mem, Shared.BasisChunk008.row8658_mem, Shared.BasisChunk008.row8660_mem, Shared.BasisChunk008.row8661_mem, Shared.BasisChunk008.row8662_mem, Shared.BasisChunk008.row8663_mem, Shared.BasisChunk008.row8664_mem, Shared.BasisChunk008.row8666_mem, Shared.BasisChunk008.row8667_mem, Shared.BasisChunk008.row8668_mem, Shared.BasisChunk008.row8669_mem, Shared.BasisChunk008.row8670_mem, Shared.BasisChunk008.row8671_mem, Shared.BasisChunk008.row8672_mem, Shared.BasisChunk008.row8675_mem, Shared.BasisChunk008.row8676_mem, Shared.BasisChunk008.row8678_mem, Shared.BasisChunk008.row8679_mem, Shared.BasisChunk008.row8680_mem, Shared.BasisChunk008.row8681_mem, Shared.BasisChunk008.row8682_mem, Shared.BasisChunk008.row8683_mem, Shared.BasisChunk008.row8684_mem, Shared.BasisChunk008.row8685_mem, Shared.BasisChunk008.row8686_mem, Shared.BasisChunk008.row8687_mem, Shared.BasisChunk008.row8689_mem, Shared.BasisChunk008.row8690_mem, Shared.BasisChunk008.row8691_mem, Shared.BasisChunk008.row8692_mem, Shared.BasisChunk008.row8694_mem, Shared.BasisChunk008.row8695_mem, Shared.BasisChunk008.row8696_mem, Shared.BasisChunk008.row8699_mem, Shared.BasisChunk008.row8700_mem, Shared.BasisChunk008.row8701_mem, Shared.BasisChunk008.row8703_mem, Shared.BasisChunk008.row8704_mem, Shared.BasisChunk008.row8706_mem, Shared.BasisChunk008.row8707_mem, Shared.BasisChunk008.row8708_mem, Shared.BasisChunk008.row8709_mem, Shared.BasisChunk008.row8710_mem, Shared.BasisChunk008.row8712_mem, Shared.BasisChunk008.row8713_mem, Shared.BasisChunk008.row8714_mem, Shared.BasisChunk008.row8715_mem, Shared.BasisChunk008.row8716_mem, Shared.BasisChunk008.row8717_mem, Shared.BasisChunk008.row8718_mem, Shared.BasisChunk008.row8720_mem, Shared.BasisChunk008.row8721_mem, Shared.BasisChunk008.row8722_mem, Shared.BasisChunk008.row8723_mem, Shared.BasisChunk008.row8724_mem, Shared.BasisChunk008.row8727_mem, Shared.BasisChunk008.row8728_mem, Shared.BasisChunk008.row8729_mem, Shared.BasisChunk008.row8730_mem, Shared.BasisChunk008.row8731_mem, Shared.BasisChunk008.row8732_mem, Shared.BasisChunk008.row8733_mem, Shared.BasisChunk008.row8734_mem, Shared.BasisChunk008.row8735_mem, Shared.BasisChunk008.row8736_mem, Shared.BasisChunk008.row8737_mem, Shared.BasisChunk008.row8738_mem, Shared.BasisChunk008.row8739_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard114
