module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard057
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk015
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk004

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard057
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard057
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
  exact ⟨Shared.RelationChunk000.relation6_zero, Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation16_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation65_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation91_zero, Shared.RelationChunk001.relation201_zero, Shared.RelationChunk008.relation472_zero, Shared.RelationChunk008.relation481_zero, Shared.RelationChunk009.relation488_zero, Shared.RelationChunk009.relation489_zero, Shared.RelationChunk009.relation509_zero, Shared.RelationChunk009.relation510_zero, Shared.RelationChunk009.relation511_zero, Shared.RelationChunk009.relation512_zero, Shared.RelationChunk009.relation513_zero, Shared.RelationChunk009.relation514_zero, Shared.RelationChunk009.relation515_zero, Shared.RelationChunk009.relation516_zero, Shared.RelationChunk009.relation519_zero, Shared.RelationChunk009.relation520_zero, Shared.RelationChunk015.relation779_zero, Shared.RelationChunk016.relation801_zero, Shared.RelationChunk016.relation805_zero, Shared.RelationChunk016.relation806_zero, Shared.RelationChunk016.relation807_zero, Shared.RelationChunk016.relation808_zero, Shared.RelationChunk016.relation809_zero, Shared.RelationChunk016.relation810_zero, Shared.RelationChunk016.relation811_zero, Shared.RelationChunk017.relation812_zero, Shared.RelationChunk017.relation813_zero, Shared.RelationChunk017.relation814_zero, Shared.RelationChunk017.relation815_zero, Shared.RelationChunk017.relation816_zero, Shared.RelationChunk017.relation817_zero, Shared.RelationChunk017.relation818_zero, Shared.RelationChunk017.relation819_zero, Shared.RelationChunk017.relation820_zero, Shared.RelationChunk017.relation821_zero, Shared.RelationChunk017.relation822_zero, Shared.RelationChunk017.relation823_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 7298 128 := by cbv
private def targetRows : List BasisRow := [⟨10, 154, 2, "2,1,565,1"⟩,
  ⟨10, 154, 3, "0,2,577,1"⟩,
  ⟨9, 154, 1, "2,1,566,1"⟩,
  ⟨9, 154, 2, "2,1,7,1,396,1"⟩,
  ⟨8, 154, 0, "13,1,341,1"⟩,
  ⟨8, 154, 2, "2,1,7,1,398,1"⟩,
  ⟨8, 154, 3, "0,1,584,1"⟩,
  ⟨8, 154, 4, "0,2,3,1,506,1"⟩,
  ⟨7, 154, 2, "2,1,7,1,400,1"⟩,
  ⟨7, 154, 3, "1,1,3,1,506,1"⟩,
  ⟨7, 154, 4, "0,2,13,1,324,1"⟩,
  ⟨6, 154, 1, "2,2,527,1"⟩,
  ⟨6, 154, 2, "1,1,13,1,324,1"⟩,
  ⟨5, 154, 0, "2,1,11,1,324,1"⟩,
  ⟨155, 155, 0, "0,155"⟩,
  ⟨52, 155, 0, "0,5,554,1"⟩,
  ⟨50, 155, 0, "0,2,578,1"⟩,
  ⟨49, 155, 0, "0,2,579,1"⟩,
  ⟨40, 155, 0, "0,2,8,1,402,1"⟩,
  ⟨39, 155, 0, "0,2,8,1,403,1"⟩,
  ⟨35, 155, 0, "0,2,8,2,16,1,138,1"⟩,
  ⟨33, 155, 0, "597,1"⟩,
  ⟨33, 155, 1, "0,5,64,1,137,1"⟩,
  ⟨32, 155, 0, "8,2,257,1"⟩,
  ⟨32, 155, 1, "0,5,64,1,138,1"⟩,
  ⟨31, 155, 0, "8,1,17,1,206,1"⟩,
  ⟨30, 155, 0, "8,2,258,1"⟩,
  ⟨30, 155, 1, "0,5,558,1"⟩,
  ⟨29, 155, 0, "8,2,259,1"⟩,
  ⟨29, 155, 1, "0,2,64,1,147,1"⟩,
  ⟨29, 155, 2, "0,11,500,1"⟩,
  ⟨28, 155, 0, "8,3,180,1"⟩,
  ⟨28, 155, 1, "0,27,324,1"⟩,
  ⟨27, 155, 0, "8,2,9,1,167,1"⟩,
  ⟨26, 155, 1, "8,1,9,1,248,1"⟩,
  ⟨25, 155, 0, "598,1"⟩,
  ⟨25, 155, 1, "16,1,292,1"⟩,
  ⟨25, 155, 2, "9,1,13,1,219,1"⟩,
  ⟨24, 155, 0, "599,1"⟩,
  ⟨24, 155, 1, "17,1,292,1"⟩,
  ⟨23, 155, 0, "602,1"⟩,
  ⟨23, 155, 1, "601,1"⟩,
  ⟨23, 155, 3, "8,1,420,1"⟩,
  ⟨22, 155, 0, "13,1,346,1"⟩,
  ⟨22, 155, 1, "8,1,16,1,209,1"⟩,
  ⟨22, 155, 2, "0,1,586,1"⟩,
  ⟨22, 155, 3, "0,4,69,1,138,1"⟩,
  ⟨21, 155, 0, "8,1,17,1,209,1"⟩,
  ⟨21, 155, 2, "0,4,568,1"⟩,
  ⟨20, 155, 1, "8,2,261,1"⟩,
  ⟨20, 155, 2, "0,1,18,1,278,1"⟩,
  ⟨19, 155, 1, "8,1,423,1"⟩,
  ⟨19, 155, 2, "0,1,69,1,147,1"⟩,
  ⟨19, 155, 3, "0,2,582,1"⟩,
  ⟨18, 155, 0, "13,2,209,1"⟩,
  ⟨18, 155, 1, "0,1,588,1"⟩,
  ⟨17, 155, 0, "13,1,67,1,75,1"⟩,
  ⟨16, 155, 1, "8,1,425,1"⟩,
  ⟨16, 155, 2, "0,5,562,1"⟩,
  ⟨15, 155, 0, "1,1,4,1,486,1"⟩,
  ⟨15, 155, 1, "0,2,8,1,414,1"⟩,
  ⟨15, 155, 2, "0,3,575,1"⟩,
  ⟨14, 155, 0, "0,1,589,1"⟩,
  ⟨14, 155, 1, "0,2,8,1,415,1"⟩,
  ⟨12, 155, 0, "2,1,570,1"⟩,
  ⟨12, 155, 1, "0,1,3,1,521,1"⟩,
  ⟨11, 155, 0, "13,1,69,1,75,1"⟩,
  ⟨11, 155, 1, "7,1,450,1"⟩,
  ⟨11, 155, 2, "0,1,3,1,523,1"⟩,
  ⟨11, 155, 3, "0,3,577,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk004.row4376_mem, Shared.BasisChunk004.row4377_mem, Shared.BasisChunk004.row4379_mem, Shared.BasisChunk004.row4380_mem, Shared.BasisChunk004.row4382_mem, Shared.BasisChunk004.row4384_mem, Shared.BasisChunk004.row4385_mem, Shared.BasisChunk004.row4386_mem, Shared.BasisChunk004.row4389_mem, Shared.BasisChunk004.row4390_mem, Shared.BasisChunk004.row4391_mem, Shared.BasisChunk004.row4393_mem, Shared.BasisChunk004.row4394_mem, Shared.BasisChunk004.row4395_mem, Shared.BasisChunk004.row4396_mem, Shared.BasisChunk004.row4397_mem, Shared.BasisChunk004.row4399_mem, Shared.BasisChunk004.row4400_mem, Shared.BasisChunk004.row4401_mem, Shared.BasisChunk004.row4402_mem, Shared.BasisChunk004.row4404_mem, Shared.BasisChunk004.row4406_mem, Shared.BasisChunk004.row4407_mem, Shared.BasisChunk004.row4408_mem, Shared.BasisChunk004.row4409_mem, Shared.BasisChunk004.row4410_mem, Shared.BasisChunk004.row4411_mem, Shared.BasisChunk004.row4412_mem, Shared.BasisChunk004.row4413_mem, Shared.BasisChunk004.row4414_mem, Shared.BasisChunk004.row4415_mem, Shared.BasisChunk004.row4416_mem, Shared.BasisChunk004.row4417_mem, Shared.BasisChunk004.row4418_mem, Shared.BasisChunk004.row4420_mem, Shared.BasisChunk004.row4422_mem, Shared.BasisChunk004.row4423_mem, Shared.BasisChunk004.row4424_mem, Shared.BasisChunk004.row4425_mem, Shared.BasisChunk004.row4426_mem, Shared.BasisChunk004.row4427_mem, Shared.BasisChunk004.row4428_mem, Shared.BasisChunk004.row4430_mem, Shared.BasisChunk004.row4431_mem, Shared.BasisChunk004.row4432_mem, Shared.BasisChunk004.row4433_mem, Shared.BasisChunk004.row4434_mem, Shared.BasisChunk004.row4435_mem, Shared.BasisChunk004.row4437_mem, Shared.BasisChunk004.row4439_mem, Shared.BasisChunk004.row4440_mem, Shared.BasisChunk004.row4442_mem, Shared.BasisChunk004.row4443_mem, Shared.BasisChunk004.row4444_mem, Shared.BasisChunk004.row4445_mem, Shared.BasisChunk004.row4446_mem, Shared.BasisChunk004.row4447_mem, Shared.BasisChunk004.row4449_mem, Shared.BasisChunk004.row4450_mem, Shared.BasisChunk004.row4451_mem, Shared.BasisChunk004.row4452_mem, Shared.BasisChunk004.row4453_mem, Shared.BasisChunk004.row4454_mem, Shared.BasisChunk004.row4455_mem, Shared.BasisChunk004.row4456_mem, Shared.BasisChunk004.row4457_mem, Shared.BasisChunk004.row4458_mem, Shared.BasisChunk004.row4459_mem, Shared.BasisChunk004.row4460_mem, Shared.BasisChunk004.row4461_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard057
