import KIP126.LinProgram.Generated.Naturality.Words200.Shard030
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk004
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard030
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard030
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation12_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation92_zero, Shared.RelationChunk000.relation129_zero, Shared.RelationChunk000.relation130_zero, Shared.RelationChunk000.relation132_zero, Shared.RelationChunk000.relation133_zero, Shared.RelationChunk000.relation135_zero, Shared.RelationChunk000.relation136_zero, Shared.RelationChunk000.relation137_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk002.relation218_zero, Shared.RelationChunk002.relation220_zero, Shared.RelationChunk002.relation221_zero, Shared.RelationChunk004.relation291_zero, Shared.RelationChunk004.relation292_zero, Shared.RelationChunk004.relation293_zero, Shared.RelationChunk004.relation297_zero, Shared.RelationChunk004.relation298_zero, Shared.RelationChunk007.relation414_zero, Shared.RelationChunk007.relation423_zero, Shared.RelationChunk007.relation424_zero, Shared.RelationChunk007.relation425_zero, Shared.RelationChunk007.relation427_zero, Shared.RelationChunk007.relation428_zero, Shared.RelationChunk007.relation429_zero, Shared.RelationChunk007.relation430_zero, Shared.RelationChunk007.relation431_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3842 128 := by cbv
private def targetRows : List BasisRow := [⟨16, 128, 2, "0,1,2,1,286,1"⟩,
  ⟨16, 128, 3, "0,2,306,1"⟩,
  ⟨15, 128, 0, "3,1,267,1"⟩,
  ⟨15, 128, 1, "1,1,13,1,189,1"⟩,
  ⟨14, 128, 0, "67,2"⟩,
  ⟨14, 128, 1, "9,1,209,1"⟩,
  ⟨13, 128, 1, "67,1,68,1"⟩,
  ⟨12, 128, 0, "68,2"⟩,
  ⟨12, 128, 1, "0,1,64,1,69,1"⟩,
  ⟨11, 128, 1, "0,1,312,1"⟩,
  ⟨11, 128, 2, "0,1,311,1"⟩,
  ⟨10, 128, 2, "0,1,314,1"⟩,
  ⟨7, 128, 1, "68,1,69,1"⟩,
  ⟨129, 129, 0, "0,129"⟩,
  ⟨42, 129, 0, "0,3,296,1"⟩,
  ⟨39, 129, 0, "326,1"⟩,
  ⟨35, 129, 0, "8,2,153,1"⟩,
  ⟨35, 129, 1, "0,13,245,1"⟩,
  ⟨34, 129, 0, "8,1,17,1,117,1"⟩,
  ⟨34, 129, 1, "0,13,246,1"⟩,
  ⟨33, 129, 0, "8,1,223,1"⟩,
  ⟨33, 129, 1, "0,3,297,1"⟩,
  ⟨32, 129, 0, "8,4,55,1"⟩,
  ⟨31, 129, 0, "8,4,56,1"⟩,
  ⟨30, 129, 1, "8,3,17,1,40,1"⟩,
  ⟨29, 129, 0, "8,1,225,1"⟩,
  ⟨29, 129, 1, "8,3,100,1"⟩,
  ⟨28, 129, 0, "8,6,9,1"⟩,
  ⟨27, 129, 0, "8,5,29,1"⟩,
  ⟨26, 129, 1, "8,4,9,1,23,1"⟩,
  ⟨25, 129, 0, "8,2,17,1,64,1"⟩,
  ⟨25, 129, 1, "8,3,9,1,51,1"⟩,
  ⟨24, 129, 0, "8,2,154,1"⟩,
  ⟨24, 129, 1, "8,2,9,1,13,3"⟩,
  ⟨23, 129, 0, "8,1,42,1,64,1"⟩,
  ⟨23, 129, 1, "8,1,9,1,13,2,32,1"⟩,
  ⟨23, 129, 2, "0,3,64,2"⟩,
  ⟨22, 129, 0, "9,1,13,3,23,1"⟩,
  ⟨22, 129, 1, "8,3,101,1"⟩,
  ⟨22, 129, 2, "0,3,299,1"⟩,
  ⟨21, 129, 0, "8,2,13,1,80,1"⟩,
  ⟨21, 129, 1, "0,4,292,1"⟩,
  ⟨20, 129, 1, "8,1,23,1,101,1"⟩,
  ⟨20, 129, 2, "0,3,301,1"⟩,
  ⟨20, 129, 3, "0,3,300,1"⟩,
  ⟨19, 129, 0, "327,1"⟩,
  ⟨19, 129, 1, "13,1,23,1,80,1"⟩,
  ⟨19, 129, 2, "0,1,317,1"⟩,
  ⟨19, 129, 3, "0,1,316,1"⟩,
  ⟨18, 129, 0, "2,1,292,1"⟩,
  ⟨17, 129, 0, "0,1,318,1"⟩,
  ⟨17, 129, 1, "0,1,3,1,266,1"⟩,
  ⟨16, 129, 1, "0,1,3,1,267,1"⟩,
  ⟨15, 129, 1, "0,1,67,2"⟩,
  ⟨14, 129, 0, "0,1,319,1"⟩,
  ⟨14, 129, 1, "0,1,67,1,68,1"⟩,
  ⟨13, 129, 0, "329,1"⟩,
  ⟨13, 129, 1, "0,1,68,2"⟩,
  ⟨13, 129, 2, "0,2,64,1,69,1"⟩,
  ⟨12, 129, 0, "330,1"⟩,
  ⟨12, 129, 2, "0,2,312,1"⟩,
  ⟨12, 129, 3, "0,2,311,1"⟩,
  ⟨11, 129, 0, "331,1"⟩,
  ⟨11, 129, 1, "0,1,3,1,270,1"⟩,
  ⟨11, 129, 2, "0,2,314,1"⟩,
  ⟨10, 129, 0, "332,1"⟩,
  ⟨10, 129, 1, "0,1,322,1"⟩,
  ⟨8, 129, 0, "0,1,68,1,69,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2293_mem, Shared.BasisChunk002.row2294_mem, Shared.BasisChunk002.row2295_mem, Shared.BasisChunk002.row2296_mem, Shared.BasisChunk002.row2297_mem, Shared.BasisChunk002.row2298_mem, Shared.BasisChunk002.row2301_mem, Shared.BasisChunk002.row2302_mem, Shared.BasisChunk002.row2303_mem, Shared.BasisChunk002.row2305_mem, Shared.BasisChunk002.row2306_mem, Shared.BasisChunk002.row2309_mem, Shared.BasisChunk002.row2313_mem, Shared.BasisChunk002.row2316_mem, Shared.BasisChunk002.row2317_mem, Shared.BasisChunk002.row2319_mem, Shared.BasisChunk002.row2321_mem, Shared.BasisChunk002.row2322_mem, Shared.BasisChunk002.row2323_mem, Shared.BasisChunk002.row2324_mem, Shared.BasisChunk002.row2325_mem, Shared.BasisChunk002.row2326_mem, Shared.BasisChunk002.row2327_mem, Shared.BasisChunk002.row2328_mem, Shared.BasisChunk002.row2330_mem, Shared.BasisChunk002.row2331_mem, Shared.BasisChunk002.row2332_mem, Shared.BasisChunk002.row2333_mem, Shared.BasisChunk002.row2334_mem, Shared.BasisChunk002.row2336_mem, Shared.BasisChunk002.row2337_mem, Shared.BasisChunk002.row2338_mem, Shared.BasisChunk002.row2339_mem, Shared.BasisChunk002.row2340_mem, Shared.BasisChunk002.row2341_mem, Shared.BasisChunk002.row2342_mem, Shared.BasisChunk002.row2343_mem, Shared.BasisChunk002.row2344_mem, Shared.BasisChunk002.row2345_mem, Shared.BasisChunk002.row2346_mem, Shared.BasisChunk002.row2347_mem, Shared.BasisChunk002.row2348_mem, Shared.BasisChunk002.row2350_mem, Shared.BasisChunk002.row2351_mem, Shared.BasisChunk002.row2352_mem, Shared.BasisChunk002.row2353_mem, Shared.BasisChunk002.row2354_mem, Shared.BasisChunk002.row2355_mem, Shared.BasisChunk002.row2356_mem, Shared.BasisChunk002.row2357_mem, Shared.BasisChunk002.row2358_mem, Shared.BasisChunk002.row2359_mem, Shared.BasisChunk002.row2361_mem, Shared.BasisChunk002.row2363_mem, Shared.BasisChunk002.row2364_mem, Shared.BasisChunk002.row2365_mem, Shared.BasisChunk002.row2366_mem, Shared.BasisChunk002.row2367_mem, Shared.BasisChunk002.row2368_mem, Shared.BasisChunk002.row2369_mem, Shared.BasisChunk002.row2371_mem, Shared.BasisChunk002.row2372_mem, Shared.BasisChunk002.row2373_mem, Shared.BasisChunk002.row2374_mem, Shared.BasisChunk002.row2375_mem, Shared.BasisChunk002.row2376_mem, Shared.BasisChunk002.row2377_mem, Shared.BasisChunk002.row2379_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard030
