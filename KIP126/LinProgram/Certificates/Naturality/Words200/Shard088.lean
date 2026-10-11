module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard088
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk031
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard088
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard088
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
  exact ⟨Shared.RelationChunk000.relation2_zero, Shared.RelationChunk000.relation56_zero, Shared.RelationChunk015.relation787_zero, Shared.RelationChunk015.relation788_zero, Shared.RelationChunk019.relation881_zero, Shared.RelationChunk019.relation882_zero, Shared.RelationChunk031.relation1314_zero, Shared.RelationChunk031.relation1315_zero, Shared.RelationChunk031.relation1316_zero, Shared.RelationChunk031.relation1317_zero, Shared.RelationChunk031.relation1319_zero, Shared.RelationChunk031.relation1320_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 11266 128 := by cbv
private def targetRows : List BasisRow := [⟨19, 177, 5, "0,1,3,2,648,1"⟩,
  ⟨18, 177, 0, "42,1,333,1"⟩,
  ⟨18, 177, 1, "13,2,332,1"⟩,
  ⟨18, 177, 2, "1,1,18,1,494,1"⟩,
  ⟨18, 177, 3, "0,1,838,1"⟩,
  ⟨17, 177, 0, "8,2,479,1"⟩,
  ⟨17, 177, 1, "1,1,41,1,324,1"⟩,
  ⟨17, 177, 2, "0,2,825,1"⟩,
  ⟨16, 177, 0, "3,1,76,1,189,1"⟩,
  ⟨16, 177, 1, "1,1,825,1"⟩,
  ⟨16, 177, 2, "0,1,841,1"⟩,
  ⟨15, 177, 0, "0,1,843,1"⟩,
  ⟨15, 177, 1, "0,1,18,1,502,1"⟩,
  ⟨15, 177, 2, "0,3,3,1,719,1"⟩,
  ⟨14, 177, 0, "3,1,76,1,190,1"⟩,
  ⟨14, 177, 1, "1,1,3,1,732,1"⟩,
  ⟨14, 177, 2, "0,1,845,1"⟩,
  ⟨14, 177, 3, "0,1,8,1,16,1,324,1"⟩,
  ⟨14, 177, 4, "0,2,826,1"⟩,
  ⟨13, 177, 0, "859,1"⟩,
  ⟨13, 177, 4, "0,1,8,1,17,1,324,1"⟩,
  ⟨12, 177, 0, "861,1"⟩,
  ⟨12, 177, 2, "3,1,755,1"⟩,
  ⟨12, 177, 3, "0,1,7,1,68,1,163,1"⟩,
  ⟨11, 177, 0, "3,1,757,1"⟩,
  ⟨11, 177, 1, "3,1,756,1"⟩,
  ⟨11, 177, 2, "0,1,846,1"⟩,
  ⟨11, 177, 3, "0,1,18,1,504,1"⟩,
  ⟨10, 177, 0, "2,1,802,1"⟩,
  ⟨10, 177, 1, "0,1,847,1"⟩,
  ⟨9, 177, 0, "0,1,848,1"⟩,
  ⟨8, 177, 0, "0,1,6,1,18,1,324,1"⟩,
  ⟨8, 177, 1, "0,1,3,1,749,1"⟩,
  ⟨7, 177, 0, "0,1,18,1,506,1"⟩,
  ⟨7, 177, 1, "0,1,3,1,750,1"⟩,
  ⟨6, 177, 0, "0,1,43,1,324,1"⟩,
  ⟨6, 177, 1, "0,1,3,1,751,1"⟩,
  ⟨5, 177, 0, "0,1,849,1"⟩,
  ⟨5, 177, 1, "0,1,3,2,18,1,324,1"⟩,
  ⟨4, 177, 0, "0,1,850,1"⟩,
  ⟨178, 178, 0, "0,178"⟩,
  ⟨59, 178, 0, "0,4,804,1"⟩,
  ⟨57, 178, 0, "0,1,851,1"⟩,
  ⟨56, 178, 0, "0,1,852,1"⟩,
  ⟨52, 178, 0, "0,14,686,1"⟩,
  ⟨51, 178, 0, "0,50,324,1"⟩,
  ⟨47, 178, 0, "0,1,8,1,635,1"⟩,
  ⟨46, 178, 0, "0,1,8,1,636,1"⟩,
  ⟨43, 178, 0, "0,1,8,2,16,1,224,1"⟩,
  ⟨42, 178, 1, "0,1,8,2,16,1,225,1"⟩,
  ⟨40, 178, 0, "0,4,64,1,224,1"⟩,
  ⟨39, 178, 0, "0,4,64,1,225,1"⟩,
  ⟨38, 178, 1, "0,5,17,1,491,1"⟩,
  ⟨37, 178, 0, "0,1,64,1,237,1"⟩,
  ⟨37, 178, 1, "0,4,809,1"⟩,
  ⟨37, 178, 2, "0,4,807,1"⟩,
  ⟨36, 178, 0, "0,1,64,1,238,1"⟩,
  ⟨36, 178, 1, "0,2,8,1,623,1"⟩,
  ⟨36, 178, 2, "0,5,795,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6738_mem, Shared.BasisChunk006.row6739_mem, Shared.BasisChunk006.row6740_mem, Shared.BasisChunk006.row6741_mem, Shared.BasisChunk006.row6742_mem, Shared.BasisChunk006.row6743_mem, Shared.BasisChunk006.row6744_mem, Shared.BasisChunk006.row6745_mem, Shared.BasisChunk006.row6746_mem, Shared.BasisChunk006.row6747_mem, Shared.BasisChunk006.row6748_mem, Shared.BasisChunk006.row6749_mem, Shared.BasisChunk006.row6750_mem, Shared.BasisChunk006.row6751_mem, Shared.BasisChunk006.row6752_mem, Shared.BasisChunk006.row6753_mem, Shared.BasisChunk006.row6754_mem, Shared.BasisChunk006.row6755_mem, Shared.BasisChunk006.row6756_mem, Shared.BasisChunk006.row6757_mem, Shared.BasisChunk006.row6761_mem, Shared.BasisChunk006.row6762_mem, Shared.BasisChunk006.row6764_mem, Shared.BasisChunk006.row6765_mem, Shared.BasisChunk006.row6766_mem, Shared.BasisChunk006.row6767_mem, Shared.BasisChunk006.row6768_mem, Shared.BasisChunk006.row6769_mem, Shared.BasisChunk006.row6770_mem, Shared.BasisChunk006.row6771_mem, Shared.BasisChunk006.row6772_mem, Shared.BasisChunk006.row6773_mem, Shared.BasisChunk006.row6774_mem, Shared.BasisChunk006.row6775_mem, Shared.BasisChunk006.row6776_mem, Shared.BasisChunk006.row6777_mem, Shared.BasisChunk006.row6778_mem, Shared.BasisChunk006.row6779_mem, Shared.BasisChunk006.row6780_mem, Shared.BasisChunk006.row6781_mem, Shared.BasisChunk006.row6782_mem, Shared.BasisChunk006.row6783_mem, Shared.BasisChunk006.row6785_mem, Shared.BasisChunk006.row6786_mem, Shared.BasisChunk006.row6787_mem, Shared.BasisChunk006.row6788_mem, Shared.BasisChunk006.row6789_mem, Shared.BasisChunk006.row6790_mem, Shared.BasisChunk006.row6792_mem, Shared.BasisChunk006.row6794_mem, Shared.BasisChunk006.row6795_mem, Shared.BasisChunk006.row6796_mem, Shared.BasisChunk006.row6798_mem, Shared.BasisChunk006.row6799_mem, Shared.BasisChunk006.row6800_mem, Shared.BasisChunk006.row6801_mem, Shared.BasisChunk006.row6802_mem, Shared.BasisChunk006.row6803_mem, Shared.BasisChunk006.row6804_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard088
