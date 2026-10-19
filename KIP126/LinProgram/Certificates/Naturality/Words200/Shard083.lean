module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard083
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationsFirst
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk014
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk027
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk029
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk006

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard083
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard083
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
  exact ⟨Shared.RelationsFirst.relation1_zero, Shared.RelationChunk000.relation4_zero, Shared.RelationChunk000.relation51_zero, Shared.RelationChunk000.relation67_zero, Shared.RelationChunk000.relation68_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk000.relation118_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk003.relation263_zero, Shared.RelationChunk003.relation264_zero, Shared.RelationChunk014.relation736_zero, Shared.RelationChunk017.relation834_zero, Shared.RelationChunk017.relation836_zero, Shared.RelationChunk017.relation841_zero, Shared.RelationChunk017.relation842_zero, Shared.RelationChunk017.relation843_zero, Shared.RelationChunk027.relation1157_zero, Shared.RelationChunk027.relation1168_zero, Shared.RelationChunk027.relation1172_zero, Shared.RelationChunk028.relation1173_zero, Shared.RelationChunk029.relation1214_zero, Shared.RelationChunk029.relation1215_zero, Shared.RelationChunk029.relation1216_zero, Shared.RelationChunk029.relation1217_zero, Shared.RelationChunk029.relation1218_zero, Shared.RelationChunk029.relation1219_zero, Shared.RelationChunk029.relation1220_zero, Shared.RelationChunk029.relation1221_zero, Shared.RelationChunk029.relation1222_zero, Shared.RelationChunk029.relation1223_zero, Shared.RelationChunk029.relation1224_zero, Shared.RelationChunk029.relation1225_zero, Shared.RelationChunk029.relation1226_zero, Shared.RelationChunk029.relation1227_zero, Shared.RelationChunk029.relation1228_zero, Shared.RelationChunk029.relation1232_zero, Shared.RelationChunk029.relation1233_zero, Shared.RelationChunk029.relation1234_zero, Shared.RelationChunk029.relation1235_zero, Shared.RelationChunk029.relation1236_zero, Shared.RelationChunk029.relation1237_zero, Shared.RelationChunk029.relation1239_zero, Shared.RelationChunk029.relation1240_zero, Shared.RelationChunk029.relation1241_zero, Shared.RelationChunk029.relation1242_zero, Shared.RelationChunk029.relation1243_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 10626 128 := by cbv
private def targetRows : List BasisRow := [⟨26, 174, 0, "8,3,267,1"⟩,
  ⟨25, 174, 1, "8,2,23,1,188,1"⟩,
  ⟨25, 174, 2, "0,1,797,1"⟩,
  ⟨24, 174, 1, "811,1"⟩,
  ⟨24, 174, 2, "13,2,303,1"⟩,
  ⟨24, 174, 3, "8,1,13,2,212,1"⟩,
  ⟨24, 174, 4, "0,2,8,1,69,1,147,1"⟩,
  ⟨24, 174, 5, "0,4,64,1,209,1"⟩,
  ⟨23, 174, 0, "813,1"⟩,
  ⟨23, 174, 1, "13,3,188,1"⟩,
  ⟨23, 174, 2, "9,1,13,1,328,1"⟩,
  ⟨23, 174, 3, "1,1,785,1"⟩,
  ⟨23, 174, 4, "0,4,760,1"⟩,
  ⟨22, 174, 0, "13,3,189,1"⟩,
  ⟨22, 174, 1, "8,1,610,1"⟩,
  ⟨22, 174, 3, "0,3,780,1"⟩,
  ⟨21, 174, 0, "80,1,201,1"⟩,
  ⟨21, 174, 2, "3,1,717,1"⟩,
  ⟨21, 174, 3, "0,4,762,1"⟩,
  ⟨20, 174, 0, "13,3,190,1"⟩,
  ⟨20, 174, 1, "8,1,613,1"⟩,
  ⟨20, 174, 2, "3,2,628,1"⟩,
  ⟨20, 174, 3, "0,4,763,1"⟩,
  ⟨19, 174, 0, "9,1,13,1,331,1"⟩,
  ⟨19, 174, 1, "1,1,786,1"⟩,
  ⟨19, 174, 2, "1,1,3,1,691,1"⟩,
  ⟨18, 174, 0, "3,2,629,1"⟩,
  ⟨18, 174, 1, "0,1,3,1,707,1"⟩,
  ⟨17, 174, 0, "8,2,443,1"⟩,
  ⟨17, 174, 1, "2,1,763,1"⟩,
  ⟨17, 174, 2, "1,2,764,1"⟩,
  ⟨17, 174, 3, "0,6,743,1"⟩,
  ⟨16, 174, 0, "8,2,445,1"⟩,
  ⟨16, 174, 2, "0,1,799,1"⟩,
  ⟨16, 174, 3, "0,1,3,1,709,1"⟩,
  ⟨16, 174, 4, "0,14,18,1,324,1"⟩,
  ⟨15, 174, 0, "1,1,70,1,209,1"⟩,
  ⟨15, 174, 2, "0,1,800,1"⟩,
  ⟨15, 174, 3, "0,1,18,1,475,1"⟩,
  ⟨15, 174, 4, "0,2,787,1"⟩,
  ⟨14, 174, 1, "0,1,801,1"⟩,
  ⟨14, 174, 2, "0,1,39,1,324,1"⟩,
  ⟨14, 174, 3, "0,2,788,1"⟩,
  ⟨13, 174, 1, "13,1,565,1"⟩,
  ⟨13, 174, 2, "0,1,40,1,324,1"⟩,
  ⟨13, 174, 3, "0,1,3,1,712,1"⟩,
  ⟨13, 174, 4, "0,2,789,1"⟩,
  ⟨12, 174, 1, "816,1"⟩,
  ⟨12, 174, 2, "13,1,566,1"⟩,
  ⟨12, 174, 4, "1,1,789,1"⟩,
  ⟨12, 174, 5, "0,2,793,1"⟩,
  ⟨11, 174, 1, "2,1,773,1"⟩,
  ⟨11, 174, 3, "0,1,18,1,479,1"⟩,
  ⟨11, 174, 4, "0,4,18,1,446,1"⟩,
  ⟨10, 174, 0, "818,1"⟩,
  ⟨10, 174, 2, "0,1,802,1"⟩,
  ⟨10, 174, 3, "0,4,34,1,324,1"⟩,
  ⟨9, 174, 0, "3,1,720,1"⟩,
  ⟨9, 174, 1, "1,2,18,1,446,1"⟩,
  ⟨9, 174, 2, "0,2,36,1,324,1"⟩,
  ⟨8, 174, 1, "1,1,36,1,324,1"⟩,
  ⟨8, 174, 2, "0,1,3,1,18,1,378,1"⟩,
  ⟨7, 174, 1, "0,2,37,1,324,1"⟩,
  ⟨6, 174, 0, "0,2,38,1,324,1"⟩,
  ⟨175, 175, 0, "0,175"⟩,
  ⟨57, 175, 0, "0,1,803,1"⟩,
  ⟨56, 175, 0, "0,1,804,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk006.row6360_mem, Shared.BasisChunk006.row6363_mem, Shared.BasisChunk006.row6364_mem, Shared.BasisChunk006.row6366_mem, Shared.BasisChunk006.row6367_mem, Shared.BasisChunk006.row6368_mem, Shared.BasisChunk006.row6369_mem, Shared.BasisChunk006.row6370_mem, Shared.BasisChunk006.row6371_mem, Shared.BasisChunk006.row6372_mem, Shared.BasisChunk006.row6373_mem, Shared.BasisChunk006.row6374_mem, Shared.BasisChunk006.row6375_mem, Shared.BasisChunk006.row6376_mem, Shared.BasisChunk006.row6377_mem, Shared.BasisChunk006.row6379_mem, Shared.BasisChunk006.row6380_mem, Shared.BasisChunk006.row6382_mem, Shared.BasisChunk006.row6383_mem, Shared.BasisChunk006.row6384_mem, Shared.BasisChunk006.row6385_mem, Shared.BasisChunk006.row6386_mem, Shared.BasisChunk006.row6387_mem, Shared.BasisChunk006.row6388_mem, Shared.BasisChunk006.row6389_mem, Shared.BasisChunk006.row6390_mem, Shared.BasisChunk006.row6391_mem, Shared.BasisChunk006.row6392_mem, Shared.BasisChunk006.row6393_mem, Shared.BasisChunk006.row6394_mem, Shared.BasisChunk006.row6395_mem, Shared.BasisChunk006.row6396_mem, Shared.BasisChunk006.row6397_mem, Shared.BasisChunk006.row6399_mem, Shared.BasisChunk006.row6400_mem, Shared.BasisChunk006.row6401_mem, Shared.BasisChunk006.row6402_mem, Shared.BasisChunk006.row6404_mem, Shared.BasisChunk006.row6405_mem, Shared.BasisChunk006.row6406_mem, Shared.BasisChunk006.row6408_mem, Shared.BasisChunk006.row6409_mem, Shared.BasisChunk006.row6410_mem, Shared.BasisChunk006.row6412_mem, Shared.BasisChunk006.row6413_mem, Shared.BasisChunk006.row6414_mem, Shared.BasisChunk006.row6415_mem, Shared.BasisChunk006.row6417_mem, Shared.BasisChunk006.row6418_mem, Shared.BasisChunk006.row6420_mem, Shared.BasisChunk006.row6421_mem, Shared.BasisChunk006.row6423_mem, Shared.BasisChunk006.row6425_mem, Shared.BasisChunk006.row6426_mem, Shared.BasisChunk006.row6427_mem, Shared.BasisChunk006.row6429_mem, Shared.BasisChunk006.row6430_mem, Shared.BasisChunk006.row6431_mem, Shared.BasisChunk006.row6432_mem, Shared.BasisChunk006.row6433_mem, Shared.BasisChunk006.row6435_mem, Shared.BasisChunk006.row6436_mem, Shared.BasisChunk006.row6438_mem, Shared.BasisChunk006.row6439_mem, Shared.BasisChunk006.row6440_mem, Shared.BasisChunk006.row6441_mem, Shared.BasisChunk006.row6442_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard083
