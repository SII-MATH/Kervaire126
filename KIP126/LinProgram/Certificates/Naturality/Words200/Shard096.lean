import KIP126.LinProgram.Generated.Naturality.Words200.Shard096
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk016
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk019
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk023
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk030
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk034
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk035
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk036
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk037
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk038
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk007

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard096
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard096
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation59_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation71_zero, Shared.RelationChunk000.relation72_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation88_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, Shared.RelationChunk001.relation147_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation207_zero, Shared.RelationChunk001.relation208_zero, Shared.RelationChunk002.relation218_zero, Shared.RelationChunk002.relation220_zero, Shared.RelationChunk002.relation221_zero, Shared.RelationChunk004.relation293_zero, Shared.RelationChunk004.relation295_zero, Shared.RelationChunk004.relation296_zero, Shared.RelationChunk004.relation297_zero, Shared.RelationChunk004.relation298_zero, Shared.RelationChunk005.relation328_zero, Shared.RelationChunk005.relation330_zero, Shared.RelationChunk005.relation352_zero, Shared.RelationChunk005.relation353_zero, Shared.RelationChunk006.relation406_zero, Shared.RelationChunk007.relation423_zero, Shared.RelationChunk007.relation425_zero, Shared.RelationChunk007.relation427_zero, Shared.RelationChunk007.relation428_zero, Shared.RelationChunk007.relation429_zero, Shared.RelationChunk007.relation430_zero, Shared.RelationChunk013.relation685_zero, Shared.RelationChunk013.relation686_zero, Shared.RelationChunk013.relation687_zero, Shared.RelationChunk013.relation688_zero, Shared.RelationChunk016.relation795_zero, Shared.RelationChunk019.relation902_zero, Shared.RelationChunk019.relation903_zero, Shared.RelationChunk023.relation1003_zero, Shared.RelationChunk023.relation1004_zero, Shared.RelationChunk023.relation1005_zero, Shared.RelationChunk023.relation1006_zero, Shared.RelationChunk030.relation1284_zero, Shared.RelationChunk034.relation1399_zero, Shared.RelationChunk035.relation1440_zero, Shared.RelationChunk035.relation1441_zero, Shared.RelationChunk035.relation1442_zero, Shared.RelationChunk036.relation1454_zero, Shared.RelationChunk036.relation1455_zero, Shared.RelationChunk036.relation1476_zero, Shared.RelationChunk036.relation1477_zero, Shared.RelationChunk036.relation1478_zero, Shared.RelationChunk036.relation1479_zero, Shared.RelationChunk037.relation1515_zero, Shared.RelationChunk037.relation1516_zero, Shared.RelationChunk037.relation1517_zero, Shared.RelationChunk037.relation1518_zero, Shared.RelationChunk037.relation1519_zero, Shared.RelationChunk037.relation1520_zero, Shared.RelationChunk038.relation1521_zero, Shared.RelationChunk038.relation1522_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 12290 128 := by cbv
private def targetRows : List BasisRow := [⟨16, 182, 1, "50,1,324,1"⟩,
  ⟨14, 182, 0, "911,1"⟩,
  ⟨14, 182, 2, "0,3,884,1"⟩,
  ⟨13, 182, 0, "8,1,18,1,367,1"⟩,
  ⟨13, 182, 3, "3,2,719,1"⟩,
  ⟨13, 182, 4, "0,4,7,1,676,1"⟩,
  ⟨12, 182, 0, "912,1"⟩,
  ⟨12, 182, 1, "43,1,392,1"⟩,
  ⟨12, 182, 2, "8,1,696,1"⟩,
  ⟨12, 182, 3, "8,1,22,1,324,1"⟩,
  ⟨12, 182, 4, "0,1,893,1"⟩,
  ⟨11, 182, 0, "43,1,397,1"⟩,
  ⟨11, 182, 1, "43,1,396,1"⟩,
  ⟨11, 182, 3, "8,1,23,1,324,1"⟩,
  ⟨11, 182, 4, "3,1,818,1"⟩,
  ⟨10, 182, 0, "51,1,324,1"⟩,
  ⟨10, 182, 1, "43,1,399,1"⟩,
  ⟨10, 182, 2, "43,1,398,1"⟩,
  ⟨10, 182, 3, "18,1,565,1"⟩,
  ⟨10, 182, 4, "0,2,7,1,698,1"⟩,
  ⟨10, 182, 5, "0,6,849,1"⟩,
  ⟨9, 182, 0, "52,1,324,1"⟩,
  ⟨9, 182, 1, "43,1,400,1"⟩,
  ⟨9, 182, 2, "9,1,660,1"⟩,
  ⟨9, 182, 4, "0,6,850,1"⟩,
  ⟨8, 182, 0, "1,2,8,1,18,1,324,1"⟩,
  ⟨8, 182, 1, "0,1,894,1"⟩,
  ⟨7, 182, 0, "913,1"⟩,
  ⟨7, 182, 1, "0,1,9,1,18,1,324,1"⟩,
  ⟨7, 182, 2, "0,2,2,1,849,1"⟩,
  ⟨6, 182, 0, "914,1"⟩,
  ⟨6, 182, 1, "10,1,18,1,324,1"⟩,
  ⟨6, 182, 2, "0,2,2,1,850,1"⟩,
  ⟨5, 182, 0, "11,1,18,1,324,1"⟩,
  ⟨183, 183, 0, "0,183"⟩,
  ⟨57, 183, 0, "0,3,17,1,554,1"⟩,
  ⟨56, 183, 1, "0,55,324,1"⟩,
  ⟨55, 183, 0, "8,1,701,1"⟩,
  ⟨54, 183, 0, "17,1,579,1"⟩,
  ⟨53, 183, 0, "915,1"⟩,
  ⟨52, 183, 0, "8,3,325,1"⟩,
  ⟨51, 183, 0, "8,3,326,1"⟩,
  ⟨50, 183, 1, "8,2,17,1,253,1"⟩,
  ⟨49, 183, 0, "917,1"⟩,
  ⟨49, 183, 1, "8,2,528,1"⟩,
  ⟨48, 183, 0, "8,5,152,1"⟩,
  ⟨47, 183, 0, "8,5,153,1"⟩,
  ⟨46, 183, 1, "8,4,17,1,117,1"⟩,
  ⟨45, 183, 0, "8,1,16,1,403,1"⟩,
  ⟨45, 183, 1, "8,4,223,1"⟩,
  ⟨45, 183, 2, "0,1,8,1,685,1"⟩,
  ⟨44, 183, 0, "8,1,17,1,403,1"⟩,
  ⟨44, 183, 1, "8,7,55,1"⟩,
  ⟨43, 183, 1, "8,7,56,1"⟩,
  ⟨42, 183, 0, "8,4,224,1"⟩,
  ⟨42, 183, 1, "8,6,17,1,40,1"⟩,
  ⟨42, 183, 2, "0,9,807,1"⟩,
  ⟨41, 183, 0, "8,4,225,1"⟩,
  ⟨41, 183, 1, "8,6,100,1"⟩,
  ⟨41, 183, 2, "0,10,795,1"⟩,
  ⟨40, 183, 0, "8,2,16,1,17,1,138,1"⟩,
  ⟨40, 183, 1, "8,9,9,1"⟩,
  ⟨39, 183, 0, "8,2,17,2,138,1"⟩,
  ⟨39, 183, 1, "8,8,29,1"⟩,
  ⟨39, 183, 2, "0,1,896,1"⟩,
  ⟨38, 183, 1, "8,5,16,1,64,1"⟩,
  ⟨38, 183, 2, "8,7,9,1,23,1"⟩,
  ⟨38, 183, 3, "0,4,64,1,244,1"⟩,
  ⟨37, 183, 0, "8,5,17,1,64,1"⟩,
  ⟨37, 183, 1, "8,6,9,1,51,1"⟩,
  ⟨37, 183, 2, "0,4,138,1,149,1"⟩,
  ⟨36, 183, 1, "8,5,154,1"⟩,
  ⟨36, 183, 2, "8,5,9,1,13,3"⟩,
  ⟨36, 183, 4, "0,4,17,2,260,1"⟩,
  ⟨35, 183, 0, "8,1,64,1,185,1"⟩,
  ⟨35, 183, 1, "8,4,42,1,64,1"⟩,
  ⟨35, 183, 2, "8,4,9,1,13,2,32,1"⟩,
  ⟨35, 183, 3, "0,1,8,2,516,1"⟩,
  ⟨35, 183, 4, "0,4,64,1,246,1"⟩,
  ⟨35, 183, 5, "0,4,59,1,260,1"⟩,
  ⟨34, 183, 0, "8,2,529,1"⟩,
  ⟨34, 183, 1, "8,3,9,1,13,3,23,1"⟩,
  ⟨34, 183, 2, "8,6,101,1"⟩,
  ⟨34, 183, 3, "0,1,8,1,17,1,380,1"⟩,
  ⟨34, 183, 4, "0,5,862,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk007.row7328_mem, Shared.BasisChunk007.row7330_mem, Shared.BasisChunk007.row7332_mem, Shared.BasisChunk007.row7333_mem, Shared.BasisChunk007.row7336_mem, Shared.BasisChunk007.row7337_mem, Shared.BasisChunk007.row7338_mem, Shared.BasisChunk007.row7339_mem, Shared.BasisChunk007.row7340_mem, Shared.BasisChunk007.row7341_mem, Shared.BasisChunk007.row7342_mem, Shared.BasisChunk007.row7343_mem, Shared.BasisChunk007.row7344_mem, Shared.BasisChunk007.row7346_mem, Shared.BasisChunk007.row7347_mem, Shared.BasisChunk007.row7348_mem, Shared.BasisChunk007.row7349_mem, Shared.BasisChunk007.row7350_mem, Shared.BasisChunk007.row7351_mem, Shared.BasisChunk007.row7352_mem, Shared.BasisChunk007.row7353_mem, Shared.BasisChunk007.row7354_mem, Shared.BasisChunk007.row7355_mem, Shared.BasisChunk007.row7356_mem, Shared.BasisChunk007.row7358_mem, Shared.BasisChunk007.row7359_mem, Shared.BasisChunk007.row7360_mem, Shared.BasisChunk007.row7361_mem, Shared.BasisChunk007.row7362_mem, Shared.BasisChunk007.row7363_mem, Shared.BasisChunk007.row7364_mem, Shared.BasisChunk007.row7365_mem, Shared.BasisChunk007.row7366_mem, Shared.BasisChunk007.row7367_mem, Shared.BasisChunk007.row7368_mem, Shared.BasisChunk007.row7369_mem, Shared.BasisChunk007.row7371_mem, Shared.BasisChunk007.row7372_mem, Shared.BasisChunk007.row7373_mem, Shared.BasisChunk007.row7374_mem, Shared.BasisChunk007.row7375_mem, Shared.BasisChunk007.row7376_mem, Shared.BasisChunk007.row7378_mem, Shared.BasisChunk007.row7379_mem, Shared.BasisChunk007.row7380_mem, Shared.BasisChunk007.row7381_mem, Shared.BasisChunk007.row7382_mem, Shared.BasisChunk007.row7384_mem, Shared.BasisChunk007.row7385_mem, Shared.BasisChunk007.row7386_mem, Shared.BasisChunk007.row7387_mem, Shared.BasisChunk007.row7388_mem, Shared.BasisChunk007.row7389_mem, Shared.BasisChunk007.row7391_mem, Shared.BasisChunk007.row7392_mem, Shared.BasisChunk007.row7393_mem, Shared.BasisChunk007.row7394_mem, Shared.BasisChunk007.row7395_mem, Shared.BasisChunk007.row7396_mem, Shared.BasisChunk007.row7397_mem, Shared.BasisChunk007.row7398_mem, Shared.BasisChunk007.row7399_mem, Shared.BasisChunk007.row7401_mem, Shared.BasisChunk007.row7402_mem, Shared.BasisChunk007.row7403_mem, Shared.BasisChunk007.row7405_mem, Shared.BasisChunk007.row7406_mem, Shared.BasisChunk007.row7407_mem, Shared.BasisChunk007.row7408_mem, Shared.BasisChunk007.row7409_mem, Shared.BasisChunk007.row7410_mem, Shared.BasisChunk007.row7412_mem, Shared.BasisChunk007.row7413_mem, Shared.BasisChunk007.row7415_mem, Shared.BasisChunk007.row7416_mem, Shared.BasisChunk007.row7417_mem, Shared.BasisChunk007.row7418_mem, Shared.BasisChunk007.row7419_mem, Shared.BasisChunk007.row7420_mem, Shared.BasisChunk007.row7421_mem, Shared.BasisChunk007.row7422_mem, Shared.BasisChunk007.row7423_mem, Shared.BasisChunk007.row7424_mem, Shared.BasisChunk007.row7425_mem, Shared.BasisChunk007.row7426_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard096
