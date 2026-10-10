import KIP126.LinProgram.Generated.Naturality.Words200.Shard109
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk008
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk009
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk011
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk013
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk017
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk024
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk028
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk042
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk044
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk046
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk008

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard109
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard109
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation71_zero, Shared.RelationChunk000.relation72_zero, Shared.RelationChunk000.relation73_zero, Shared.RelationChunk000.relation76_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation98_zero, Shared.RelationChunk000.relation99_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk002.relation231_zero, Shared.RelationChunk002.relation237_zero, Shared.RelationChunk003.relation261_zero, Shared.RelationChunk003.relation271_zero, Shared.RelationChunk006.relation403_zero, Shared.RelationChunk007.relation418_zero, Shared.RelationChunk008.relation481_zero, Shared.RelationChunk009.relation509_zero, Shared.RelationChunk009.relation510_zero, Shared.RelationChunk009.relation511_zero, Shared.RelationChunk009.relation512_zero, Shared.RelationChunk009.relation513_zero, Shared.RelationChunk009.relation514_zero, Shared.RelationChunk009.relation515_zero, Shared.RelationChunk009.relation516_zero, Shared.RelationChunk011.relation611_zero, Shared.RelationChunk013.relation669_zero, Shared.RelationChunk013.relation671_zero, Shared.RelationChunk017.relation818_zero, Shared.RelationChunk017.relation819_zero, Shared.RelationChunk017.relation820_zero, Shared.RelationChunk017.relation821_zero, Shared.RelationChunk017.relation822_zero, Shared.RelationChunk024.relation1047_zero, Shared.RelationChunk024.relation1048_zero, Shared.RelationChunk028.relation1183_zero, Shared.RelationChunk028.relation1185_zero, Shared.RelationChunk028.relation1186_zero, Shared.RelationChunk028.relation1188_zero, Shared.RelationChunk028.relation1203_zero, Shared.RelationChunk028.relation1204_zero, Shared.RelationChunk028.relation1205_zero, Shared.RelationChunk028.relation1209_zero, Shared.RelationChunk028.relation1210_zero, Shared.RelationChunk028.relation1211_zero, Shared.RelationChunk028.relation1212_zero, Shared.RelationChunk028.relation1213_zero, Shared.RelationChunk042.relation1638_zero, Shared.RelationChunk044.relation1685_zero, Shared.RelationChunk044.relation1686_zero, Shared.RelationChunk044.relation1687_zero, Shared.RelationChunk044.relation1689_zero, Shared.RelationChunk046.relation1701_zero, Shared.RelationChunk046.relation1702_zero, Shared.RelationChunk046.relation1703_zero, Shared.RelationChunk046.relation1704_zero, Shared.RelationChunk046.relation1705_zero, Shared.RelationChunk046.relation1706_zero, Shared.RelationChunk046.relation1707_zero, Shared.RelationChunk046.relation1708_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 13954 128 := by cbv
private def targetRows : List BasisRow := [⟨19, 190, 2, "18,1,628,1"⟩,
  ⟨19, 190, 3, "9,1,23,1,373,1"⟩,
  ⟨19, 190, 5, "0,2,8,1,31,1,324,1"⟩,
  ⟨19, 190, 6, "0,3,965,1"⟩,
  ⟨18, 190, 2, "0,1,1002,1"⟩,
  ⟨18, 190, 3, "0,2,987,1"⟩,
  ⟨18, 190, 4, "0,2,16,1,17,1,324,1"⟩,
  ⟨17, 190, 1, "1015,1"⟩,
  ⟨17, 190, 2, "1,1,987,1"⟩,
  ⟨17, 190, 3, "0,2,17,2,324,1"⟩,
  ⟨16, 190, 1, "1018,1"⟩,
  ⟨16, 190, 3, "75,1,288,1"⟩,
  ⟨16, 190, 4, "1,1,989,1"⟩,
  ⟨16, 190, 6, "0,1,1005,1"⟩,
  ⟨16, 190, 7, "0,2,59,1,324,1"⟩,
  ⟨15, 190, 1, "1021,1"⟩,
  ⟨15, 190, 2, "1020,1"⟩,
  ⟨15, 190, 4, "1,1,990,1"⟩,
  ⟨15, 190, 5, "1,1,59,1,324,1"⟩,
  ⟨15, 190, 6, "0,1,1006,1"⟩,
  ⟨14, 190, 0, "1024,1"⟩,
  ⟨14, 190, 2, "1,1,992,1"⟩,
  ⟨14, 190, 3, "0,1,1008,1"⟩,
  ⟨14, 190, 4, "0,2,18,1,615,1"⟩,
  ⟨13, 190, 0, "1025,1"⟩,
  ⟨13, 190, 1, "2,1,76,1,264,1"⟩,
  ⟨13, 190, 2, "0,2,993,1"⟩,
  ⟨10, 190, 0, "1028,1"⟩,
  ⟨9, 190, 0, "17,1,18,1,324,1"⟩,
  ⟨9, 190, 1, "0,2,994,1"⟩,
  ⟨8, 190, 0, "1,1,61,1,324,1"⟩,
  ⟨191, 191, 0, "0,191"⟩,
  ⟨64, 191, 0, "0,63,324,1"⟩,
  ⟨62, 191, 0, "0,2,995,1"⟩,
  ⟨61, 191, 0, "0,2,996,1"⟩,
  ⟨58, 191, 0, "0,8,916,1"⟩,
  ⟨57, 191, 0, "0,8,917,1"⟩,
  ⟨52, 191, 0, "0,2,16,1,635,1"⟩,
  ⟨51, 191, 0, "0,2,16,1,636,1"⟩,
  ⟨51, 191, 1, "0,3,969,1"⟩,
  ⟨50, 191, 0, "0,2,17,1,636,1"⟩,
  ⟨47, 191, 0, "0,2,8,3,403,1"⟩,
  ⟨46, 191, 0, "1031,1"⟩,
  ⟨45, 191, 0, "1032,1"⟩,
  ⟨44, 191, 0, "8,2,595,1"⟩,
  ⟨43, 191, 0, "8,1,17,1,488,1"⟩,
  ⟨42, 191, 1, "8,2,596,1"⟩,
  ⟨41, 191, 0, "8,2,597,1"⟩,
  ⟨41, 191, 1, "0,2,64,1,298,1"⟩,
  ⟨40, 191, 0, "8,4,257,1"⟩,
  ⟨39, 191, 0, "8,3,17,1,206,1"⟩,
  ⟨38, 191, 1, "8,4,258,1"⟩,
  ⟨37, 191, 0, "8,1,17,1,491,1"⟩,
  ⟨37, 191, 1, "8,4,259,1"⟩,
  ⟨36, 191, 0, "1034,1"⟩,
  ⟨36, 191, 1, "8,5,180,1"⟩,
  ⟨35, 191, 1, "8,1,796,1"⟩,
  ⟨35, 191, 2, "8,4,9,1,167,1"⟩,
  ⟨35, 191, 3, "0,8,919,1"⟩,
  ⟨34, 191, 0, "8,2,64,1,149,1"⟩,
  ⟨34, 191, 1, "8,3,9,1,248,1"⟩,
  ⟨34, 191, 2, "8,4,260,1"⟩,
  ⟨34, 191, 3, "0,9,898,1"⟩,
  ⟨33, 191, 0, "8,2,598,1"⟩,
  ⟨33, 191, 1, "8,2,16,1,292,1"⟩,
  ⟨33, 191, 2, "8,2,9,1,13,1,219,1"⟩,
  ⟨32, 191, 0, "8,1,9,1,13,2,194,1"⟩,
  ⟨32, 191, 1, "8,2,599,1"⟩,
  ⟨32, 191, 2, "8,2,17,1,292,1"⟩,
  ⟨32, 191, 3, "0,2,64,3"⟩,
  ⟨31, 191, 0, "9,1,13,3,167,1"⟩,
  ⟨31, 191, 1, "8,2,602,1"⟩,
  ⟨31, 191, 2, "8,3,420,1"⟩,
  ⟨31, 191, 4, "0,2,64,1,299,1"⟩,
  ⟨30, 191, 0, "8,2,13,1,346,1"⟩,
  ⟨30, 191, 1, "8,3,16,1,209,1"⟩,
  ⟨30, 191, 2, "0,4,963,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk008.row8283_mem, Shared.BasisChunk008.row8284_mem, Shared.BasisChunk008.row8286_mem, Shared.BasisChunk008.row8287_mem, Shared.BasisChunk008.row8290_mem, Shared.BasisChunk008.row8291_mem, Shared.BasisChunk008.row8292_mem, Shared.BasisChunk008.row8294_mem, Shared.BasisChunk008.row8295_mem, Shared.BasisChunk008.row8296_mem, Shared.BasisChunk008.row8298_mem, Shared.BasisChunk008.row8300_mem, Shared.BasisChunk008.row8301_mem, Shared.BasisChunk008.row8303_mem, Shared.BasisChunk008.row8304_mem, Shared.BasisChunk008.row8306_mem, Shared.BasisChunk008.row8307_mem, Shared.BasisChunk008.row8309_mem, Shared.BasisChunk008.row8310_mem, Shared.BasisChunk008.row8311_mem, Shared.BasisChunk008.row8312_mem, Shared.BasisChunk008.row8314_mem, Shared.BasisChunk008.row8315_mem, Shared.BasisChunk008.row8316_mem, Shared.BasisChunk008.row8317_mem, Shared.BasisChunk008.row8318_mem, Shared.BasisChunk008.row8319_mem, Shared.BasisChunk008.row8322_mem, Shared.BasisChunk008.row8324_mem, Shared.BasisChunk008.row8325_mem, Shared.BasisChunk008.row8326_mem, Shared.BasisChunk008.row8327_mem, Shared.BasisChunk008.row8328_mem, Shared.BasisChunk008.row8330_mem, Shared.BasisChunk008.row8331_mem, Shared.BasisChunk008.row8332_mem, Shared.BasisChunk008.row8333_mem, Shared.BasisChunk008.row8334_mem, Shared.BasisChunk008.row8335_mem, Shared.BasisChunk008.row8336_mem, Shared.BasisChunk008.row8337_mem, Shared.BasisChunk008.row8339_mem, Shared.BasisChunk008.row8340_mem, Shared.BasisChunk008.row8341_mem, Shared.BasisChunk008.row8342_mem, Shared.BasisChunk008.row8343_mem, Shared.BasisChunk008.row8345_mem, Shared.BasisChunk008.row8346_mem, Shared.BasisChunk008.row8347_mem, Shared.BasisChunk008.row8348_mem, Shared.BasisChunk008.row8349_mem, Shared.BasisChunk008.row8351_mem, Shared.BasisChunk008.row8352_mem, Shared.BasisChunk008.row8353_mem, Shared.BasisChunk008.row8354_mem, Shared.BasisChunk008.row8355_mem, Shared.BasisChunk008.row8357_mem, Shared.BasisChunk008.row8358_mem, Shared.BasisChunk008.row8359_mem, Shared.BasisChunk008.row8360_mem, Shared.BasisChunk008.row8361_mem, Shared.BasisChunk008.row8362_mem, Shared.BasisChunk008.row8363_mem, Shared.BasisChunk008.row8364_mem, Shared.BasisChunk008.row8365_mem, Shared.BasisChunk008.row8366_mem, Shared.BasisChunk008.row8367_mem, Shared.BasisChunk008.row8368_mem, Shared.BasisChunk008.row8369_mem, Shared.BasisChunk008.row8370_mem, Shared.BasisChunk008.row8371_mem, Shared.BasisChunk008.row8372_mem, Shared.BasisChunk008.row8373_mem, Shared.BasisChunk008.row8375_mem, Shared.BasisChunk008.row8376_mem, Shared.BasisChunk008.row8377_mem, Shared.BasisChunk008.row8378_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard109
