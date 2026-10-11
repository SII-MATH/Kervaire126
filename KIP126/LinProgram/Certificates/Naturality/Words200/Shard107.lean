module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard107
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk022
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk026
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk040
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk041
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk043
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard107
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard107
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
  exact ⟨Shared.RelationChunk000.relation75_zero, Shared.RelationChunk001.relation173_zero, Shared.RelationChunk001.relation174_zero, Shared.RelationChunk001.relation180_zero, Shared.RelationChunk022.relation985_zero, Shared.RelationChunk022.relation988_zero, Shared.RelationChunk022.relation990_zero, Shared.RelationChunk022.relation992_zero, Shared.RelationChunk026.relation1136_zero, Shared.RelationChunk026.relation1137_zero, Shared.RelationChunk035.relation1443_zero, Shared.RelationChunk040.relation1582_zero, Shared.RelationChunk041.relation1609_zero, Shared.RelationChunk041.relation1624_zero, Shared.RelationChunk043.relation1658_zero, Shared.RelationChunk043.relation1659_zero, Shared.RelationChunk043.relation1661_zero, Shared.RelationChunk043.relation1662_zero, Shared.RelationChunk043.relation1663_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13698 128 := by cbv
private def targetRows : List BasisRow := [⟨26, 189, 2, "0,1,977,1"⟩,
  ⟨26, 189, 3, "0,1,976,1"⟩,
  ⟨25, 189, 0, "13,2,472,1"⟩,
  ⟨25, 189, 1, "8,1,79,1,188,1"⟩,
  ⟨25, 189, 2, "0,1,978,1"⟩,
  ⟨25, 189, 3, "0,1,13,1,690,1"⟩,
  ⟨24, 189, 1, "13,2,473,1"⟩,
  ⟨24, 189, 2, "8,1,80,1,188,1"⟩,
  ⟨24, 189, 3, "8,1,17,1,475,1"⟩,
  ⟨24, 189, 4, "2,1,941,1"⟩,
  ⟨23, 189, 1, "13,1,705,1"⟩,
  ⟨23, 189, 2, "1,1,3,1,877,1"⟩,
  ⟨23, 189, 3, "0,1,2,1,930,1"⟩,
  ⟨22, 189, 0, "999,1"⟩,
  ⟨22, 189, 1, "0,1,981,1"⟩,
  ⟨21, 189, 0, "13,2,474,1"⟩,
  ⟨21, 189, 1, "1,1,58,1,324,1"⟩,
  ⟨21, 189, 2, "0,1,982,1"⟩,
  ⟨20, 189, 0, "13,2,476,1"⟩,
  ⟨20, 189, 1, "5,1,825,1"⟩,
  ⟨20, 189, 3, "0,1,984,1"⟩,
  ⟨19, 189, 0, "1000,1"⟩,
  ⟨18, 189, 0, "1001,1"⟩,
  ⟨18, 189, 1, "0,1,8,1,31,1,324,1"⟩,
  ⟨18, 189, 2, "0,2,965,1"⟩,
  ⟨17, 189, 0, "1003,1"⟩,
  ⟨17, 189, 1, "1002,1"⟩,
  ⟨17, 189, 2, "0,1,987,1"⟩,
  ⟨17, 189, 3, "0,1,16,1,17,1,324,1"⟩,
  ⟨16, 189, 2, "0,1,17,2,324,1"⟩,
  ⟨15, 189, 0, "1005,1"⟩,
  ⟨15, 189, 1, "1,1,69,1,287,1"⟩,
  ⟨15, 189, 2, "0,1,59,1,324,1"⟩,
  ⟨14, 189, 0, "1007,1"⟩,
  ⟨14, 189, 1, "1006,1"⟩,
  ⟨13, 189, 0, "1008,1"⟩,
  ⟨13, 189, 1, "1,1,3,1,884,1"⟩,
  ⟨13, 189, 2, "0,1,18,1,615,1"⟩,
  ⟨12, 189, 0, "1,1,968,1"⟩,
  ⟨12, 189, 1, "0,1,993,1"⟩,
  ⟨9, 189, 0, "0,1,18,1,617,1"⟩,
  ⟨8, 189, 0, "1,1,4,1,849,1"⟩,
  ⟨8, 189, 1, "0,1,994,1"⟩,
  ⟨7, 189, 0, "1,1,4,1,850,1"⟩,
  ⟨190, 190, 0, "0,190"⟩,
  ⟨63, 190, 0, "0,62,324,1"⟩,
  ⟨61, 190, 0, "0,1,995,1"⟩,
  ⟨60, 190, 0, "0,1,996,1"⟩,
  ⟨57, 190, 0, "0,7,916,1"⟩,
  ⟨56, 190, 0, "0,7,917,1"⟩,
  ⟨51, 190, 0, "0,1,16,1,635,1"⟩,
  ⟨50, 190, 0, "0,1,16,1,636,1"⟩,
  ⟨50, 190, 1, "0,2,969,1"⟩,
  ⟨49, 190, 1, "0,1,17,1,636,1"⟩,
  ⟨47, 190, 0, "0,1,8,3,402,1"⟩,
  ⟨46, 190, 1, "0,1,8,3,403,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row8169_mem, Shared.BasisChunk007.row8170_mem, Shared.BasisChunk007.row8171_mem, Shared.BasisChunk007.row8172_mem, Shared.BasisChunk007.row8173_mem, Shared.BasisChunk007.row8174_mem, Shared.BasisChunk007.row8176_mem, Shared.BasisChunk007.row8177_mem, Shared.BasisChunk007.row8178_mem, Shared.BasisChunk007.row8179_mem, Shared.BasisChunk007.row8181_mem, Shared.BasisChunk007.row8182_mem, Shared.BasisChunk007.row8183_mem, Shared.BasisChunk007.row8184_mem, Shared.BasisChunk007.row8185_mem, Shared.BasisChunk007.row8186_mem, Shared.BasisChunk007.row8187_mem, Shared.BasisChunk007.row8188_mem, Shared.BasisChunk007.row8189_mem, Shared.BasisChunk007.row8190_mem, Shared.BasisChunk008.row8192_mem, Shared.BasisChunk008.row8193_mem, Shared.BasisChunk008.row8194_mem, Shared.BasisChunk008.row8195_mem, Shared.BasisChunk008.row8196_mem, Shared.BasisChunk008.row8197_mem, Shared.BasisChunk008.row8198_mem, Shared.BasisChunk008.row8199_mem, Shared.BasisChunk008.row8200_mem, Shared.BasisChunk008.row8203_mem, Shared.BasisChunk008.row8204_mem, Shared.BasisChunk008.row8205_mem, Shared.BasisChunk008.row8206_mem, Shared.BasisChunk008.row8207_mem, Shared.BasisChunk008.row8208_mem, Shared.BasisChunk008.row8209_mem, Shared.BasisChunk008.row8210_mem, Shared.BasisChunk008.row8211_mem, Shared.BasisChunk008.row8212_mem, Shared.BasisChunk008.row8213_mem, Shared.BasisChunk008.row8214_mem, Shared.BasisChunk008.row8215_mem, Shared.BasisChunk008.row8216_mem, Shared.BasisChunk008.row8217_mem, Shared.BasisChunk008.row8218_mem, Shared.BasisChunk008.row8219_mem, Shared.BasisChunk008.row8221_mem, Shared.BasisChunk008.row8222_mem, Shared.BasisChunk008.row8223_mem, Shared.BasisChunk008.row8224_mem, Shared.BasisChunk008.row8225_mem, Shared.BasisChunk008.row8226_mem, Shared.BasisChunk008.row8227_mem, Shared.BasisChunk008.row8229_mem, Shared.BasisChunk008.row8230_mem, Shared.BasisChunk008.row8232_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard107
