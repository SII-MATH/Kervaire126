module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard054
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard054
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard054
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
  exact ⟨Shared.RelationsFirst.relation0_zero, Shared.RelationChunk000.relation7_zero, Shared.RelationChunk000.relation9_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk001.relation188_zero, Shared.RelationChunk002.relation239_zero, Shared.RelationChunk002.relation240_zero, Shared.RelationChunk002.relation241_zero, Shared.RelationChunk008.relation474_zero, Shared.RelationChunk008.relation475_zero, Shared.RelationChunk008.relation476_zero, Shared.RelationChunk008.relation477_zero, Shared.RelationChunk008.relation478_zero, Shared.RelationChunk008.relation479_zero, Shared.RelationChunk008.relation480_zero, Shared.RelationChunk009.relation496_zero, Shared.RelationChunk009.relation497_zero, Shared.RelationChunk009.relation499_zero, Shared.RelationChunk009.relation500_zero, Shared.RelationChunk009.relation502_zero, Shared.RelationChunk009.relation503_zero, Shared.RelationChunk014.relation726_zero, Shared.RelationChunk014.relation728_zero, Shared.RelationChunk014.relation729_zero, Shared.RelationChunk014.relation730_zero, Shared.RelationChunk014.relation731_zero, Shared.RelationChunk015.relation755_zero, Shared.RelationChunk015.relation757_zero, Shared.RelationChunk015.relation758_zero, Shared.RelationChunk015.relation759_zero, Shared.RelationChunk015.relation760_zero, Shared.RelationChunk015.relation761_zero, Shared.RelationChunk015.relation762_zero, Shared.RelationChunk015.relation763_zero, Shared.RelationChunk015.relation764_zero, Shared.RelationChunk015.relation765_zero, Shared.RelationChunk015.relation766_zero, Shared.RelationChunk015.relation767_zero, Shared.RelationChunk015.relation768_zero, Shared.RelationChunk015.relation769_zero, Shared.RelationChunk015.relation770_zero, Shared.RelationChunk015.relation771_zero, Shared.RelationChunk015.relation772_zero, Shared.RelationChunk015.relation773_zero, Shared.RelationChunk015.relation774_zero, Shared.RelationChunk015.relation775_zero, Shared.RelationChunk015.relation776_zero, Shared.RelationChunk015.relation780_zero, Shared.RelationChunk015.relation781_zero, Shared.RelationChunk016.relation796_zero, Shared.RelationChunk016.relation797_zero, Shared.RelationChunk016.relation798_zero, Shared.RelationChunk016.relation799_zero, Shared.RelationChunk016.relation800_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 6914 128 := by cbv
private def targetRows : List BasisRow := [⟨29, 152, 2, "0,2,64,1,138,1"⟩,
  ⟨28, 152, 0, "8,3,166,1"⟩,
  ⟨28, 152, 1, "0,3,17,1,260,1"⟩,
  ⟨27, 152, 0, "8,3,167,1"⟩,
  ⟨27, 152, 1, "0,2,558,1"⟩,
  ⟨26, 152, 1, "8,2,248,1"⟩,
  ⟨26, 152, 3, "0,8,500,1"⟩,
  ⟨25, 152, 0, "17,1,278,1"⟩,
  ⟨25, 152, 1, "8,1,13,1,219,1"⟩,
  ⟨25, 152, 2, "0,24,324,1"⟩,
  ⟨24, 152, 0, "573,1"⟩,
  ⟨24, 152, 1, "13,2,194,1"⟩,
  ⟨23, 152, 0, "574,1"⟩,
  ⟨23, 152, 1, "13,1,23,1,150,1"⟩,
  ⟨22, 152, 0, "9,1,346,1"⟩,
  ⟨22, 152, 1, "8,1,382,1"⟩,
  ⟨22, 152, 2, "2,1,537,1"⟩,
  ⟨22, 152, 3, "1,1,42,1,187,1"⟩,
  ⟨21, 152, 0, "8,1,383,1"⟩,
  ⟨21, 152, 1, "2,1,538,1"⟩,
  ⟨20, 152, 0, "8,2,250,1"⟩,
  ⟨20, 152, 1, "0,1,18,1,260,1"⟩,
  ⟨19, 152, 0, "8,1,384,1"⟩,
  ⟨19, 152, 1, "1,1,560,1"⟩,
  ⟨19, 152, 2, "0,1,69,1,138,1"⟩,
  ⟨19, 152, 3, "0,2,561,1"⟩,
  ⟨18, 152, 0, "9,1,13,1,209,1"⟩,
  ⟨18, 152, 2, "0,1,568,1"⟩,
  ⟨18, 152, 3, "0,5,533,1"⟩,
  ⟨17, 152, 0, "7,2,266,1"⟩,
  ⟨17, 152, 1, "0,4,540,1"⟩,
  ⟨16, 152, 0, "7,2,267,1"⟩,
  ⟨16, 152, 1, "1,1,7,1,385,1"⟩,
  ⟨16, 152, 2, "0,1,8,1,69,1,79,1"⟩,
  ⟨15, 152, 0, "1,1,43,1,189,1"⟩,
  ⟨15, 152, 1, "1,2,540,1"⟩,
  ⟨15, 152, 2, "0,1,8,1,69,1,80,1"⟩,
  ⟨15, 152, 3, "0,2,8,1,366,1"⟩,
  ⟨15, 152, 4, "0,2,3,1,484,1"⟩,
  ⟨14, 152, 0, "2,1,540,1"⟩,
  ⟨14, 152, 1, "0,2,8,1,367,1"⟩,
  ⟨14, 152, 2, "0,2,3,1,485,1"⟩,
  ⟨13, 152, 0, "1,1,3,1,485,1"⟩,
  ⟨13, 152, 1, "0,1,569,1"⟩,
  ⟨13, 152, 2, "0,2,562,1"⟩,
  ⟨12, 152, 1, "2,1,543,1"⟩,
  ⟨12, 152, 2, "1,2,544,1"⟩,
  ⟨12, 152, 3, "0,4,546,1"⟩,
  ⟨11, 152, 0, "9,1,69,1,75,1"⟩,
  ⟨11, 152, 1, "2,1,544,1"⟩,
  ⟨11, 152, 3, "0,1,7,1,414,1"⟩,
  ⟨11, 152, 4, "0,2,7,1,394,1"⟩,
  ⟨10, 152, 1, "1,2,546,1"⟩,
  ⟨10, 152, 2, "0,1,7,1,415,1"⟩,
  ⟨10, 152, 3, "0,2,7,1,396,1"⟩,
  ⟨9, 152, 0, "576,1"⟩,
  ⟨9, 152, 1, "1,1,566,1"⟩,
  ⟨9, 152, 2, "0,1,18,1,264,1"⟩,
  ⟨9, 152, 3, "0,3,9,1,69,2"⟩,
  ⟨8, 152, 1, "2,1,7,1,368,1"⟩,
  ⟨8, 152, 2, "0,3,9,1,324,1"⟩,
  ⟨5, 152, 1, "2,1,548,1"⟩,
  ⟨4, 152, 0, "2,2,7,1,324,1"⟩,
  ⟨153, 153, 0, "0,153"⟩,
  ⟨50, 153, 0, "0,3,554,1"⟩,
  ⟨47, 153, 0, "579,1"⟩,
  ⟨44, 153, 0, "8,2,252,1"⟩,
  ⟨43, 153, 0, "8,2,253,1"⟩,
  ⟨42, 153, 0, "8,1,17,1,200,1"⟩,
  ⟨41, 153, 0, "8,1,401,1"⟩,
  ⟨41, 153, 1, "0,3,555,1"⟩,
  ⟨40, 153, 0, "8,4,116,1"⟩,
  ⟨39, 153, 0, "8,4,117,1"⟩,
  ⟨38, 153, 1, "8,3,17,1,78,1"⟩,
  ⟨37, 153, 0, "8,1,403,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4159_mem, Shared.BasisChunk004.row4160_mem, Shared.BasisChunk004.row4161_mem, Shared.BasisChunk004.row4162_mem, Shared.BasisChunk004.row4163_mem, Shared.BasisChunk004.row4165_mem, Shared.BasisChunk004.row4167_mem, Shared.BasisChunk004.row4168_mem, Shared.BasisChunk004.row4169_mem, Shared.BasisChunk004.row4170_mem, Shared.BasisChunk004.row4171_mem, Shared.BasisChunk004.row4172_mem, Shared.BasisChunk004.row4173_mem, Shared.BasisChunk004.row4174_mem, Shared.BasisChunk004.row4175_mem, Shared.BasisChunk004.row4176_mem, Shared.BasisChunk004.row4177_mem, Shared.BasisChunk004.row4178_mem, Shared.BasisChunk004.row4179_mem, Shared.BasisChunk004.row4180_mem, Shared.BasisChunk004.row4181_mem, Shared.BasisChunk004.row4182_mem, Shared.BasisChunk004.row4183_mem, Shared.BasisChunk004.row4184_mem, Shared.BasisChunk004.row4185_mem, Shared.BasisChunk004.row4186_mem, Shared.BasisChunk004.row4187_mem, Shared.BasisChunk004.row4189_mem, Shared.BasisChunk004.row4190_mem, Shared.BasisChunk004.row4191_mem, Shared.BasisChunk004.row4192_mem, Shared.BasisChunk004.row4193_mem, Shared.BasisChunk004.row4194_mem, Shared.BasisChunk004.row4195_mem, Shared.BasisChunk004.row4196_mem, Shared.BasisChunk004.row4197_mem, Shared.BasisChunk004.row4198_mem, Shared.BasisChunk004.row4199_mem, Shared.BasisChunk004.row4200_mem, Shared.BasisChunk004.row4201_mem, Shared.BasisChunk004.row4202_mem, Shared.BasisChunk004.row4203_mem, Shared.BasisChunk004.row4204_mem, Shared.BasisChunk004.row4205_mem, Shared.BasisChunk004.row4206_mem, Shared.BasisChunk004.row4208_mem, Shared.BasisChunk004.row4209_mem, Shared.BasisChunk004.row4210_mem, Shared.BasisChunk004.row4211_mem, Shared.BasisChunk004.row4212_mem, Shared.BasisChunk004.row4214_mem, Shared.BasisChunk004.row4215_mem, Shared.BasisChunk004.row4217_mem, Shared.BasisChunk004.row4218_mem, Shared.BasisChunk004.row4219_mem, Shared.BasisChunk004.row4220_mem, Shared.BasisChunk004.row4221_mem, Shared.BasisChunk004.row4222_mem, Shared.BasisChunk004.row4223_mem, Shared.BasisChunk004.row4225_mem, Shared.BasisChunk004.row4226_mem, Shared.BasisChunk004.row4229_mem, Shared.BasisChunk004.row4230_mem, Shared.BasisChunk004.row4231_mem, Shared.BasisChunk004.row4232_mem, Shared.BasisChunk004.row4234_mem, Shared.BasisChunk004.row4235_mem, Shared.BasisChunk004.row4236_mem, Shared.BasisChunk004.row4237_mem, Shared.BasisChunk004.row4238_mem, Shared.BasisChunk004.row4239_mem, Shared.BasisChunk004.row4240_mem, Shared.BasisChunk004.row4241_mem, Shared.BasisChunk004.row4243_mem, Shared.BasisChunk004.row4244_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard054
