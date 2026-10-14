module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard029
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk007
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard029
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard029
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
  exact ⟨Shared.RelationChunk007.relation407_zero, Shared.RelationChunk007.relation408_zero, Shared.RelationChunk007.relation415_zero, Shared.RelationChunk007.relation416_zero, Shared.RelationChunk007.relation417_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3714 128 := by cbv
private def targetRows : List BasisRow := [⟨30, 127, 0, "0,1,298,1"⟩,
  ⟨28, 127, 0, "0,5,17,1,149,1"⟩,
  ⟨27, 127, 0, "0,1,8,2,146,1"⟩,
  ⟨27, 127, 1, "0,4,17,1,154,1"⟩,
  ⟨26, 127, 0, "0,1,8,2,147,1"⟩,
  ⟨26, 127, 1, "0,8,260,1"⟩,
  ⟨25, 127, 0, "0,1,8,1,17,1,113,1"⟩,
  ⟨25, 127, 1, "0,6,274,1"⟩,
  ⟨21, 127, 0, "0,1,64,2"⟩,
  ⟨20, 127, 0, "0,1,299,1"⟩,
  ⟨20, 127, 1, "0,2,291,1"⟩,
  ⟨19, 127, 0, "1,1,291,1"⟩,
  ⟨19, 127, 1, "0,2,292,1"⟩,
  ⟨18, 127, 0, "0,1,301,1"⟩,
  ⟨18, 127, 1, "0,1,300,1"⟩,
  ⟨17, 127, 0, "0,1,8,1,212,1"⟩,
  ⟨17, 127, 1, "0,3,59,1,69,1"⟩,
  ⟨16, 127, 0, "13,1,23,1,75,1"⟩,
  ⟨16, 127, 2, "0,1,304,1"⟩,
  ⟨16, 127, 3, "0,1,13,1,188,1"⟩,
  ⟨15, 127, 0, "13,1,23,1,76,1"⟩,
  ⟨15, 127, 1, "2,1,286,1"⟩,
  ⟨15, 127, 2, "1,1,8,1,209,1"⟩,
  ⟨15, 127, 3, "0,1,306,1"⟩,
  ⟨14, 127, 0, "2,1,287,1"⟩,
  ⟨14, 127, 1, "0,1,308,1"⟩,
  ⟨10, 127, 0, "312,1"⟩,
  ⟨10, 127, 1, "311,1"⟩,
  ⟨9, 127, 0, "314,1"⟩,
  ⟨128, 128, 0, "0,128"⟩,
  ⟨42, 128, 0, "0,2,295,1"⟩,
  ⟨41, 128, 1, "0,2,296,1"⟩,
  ⟨38, 128, 0, "0,2,8,2,145,1"⟩,
  ⟨37, 128, 0, "0,2,8,1,16,1,111,1"⟩,
  ⟨34, 128, 0, "0,12,245,1"⟩,
  ⟨33, 128, 0, "0,12,246,1"⟩,
  ⟨32, 128, 0, "0,2,297,1"⟩,
  ⟨31, 128, 0, "0,2,298,1"⟩,
  ⟨28, 128, 0, "0,5,17,1,154,1"⟩,
  ⟨27, 128, 0, "0,2,8,2,147,1"⟩,
  ⟨24, 128, 0, "8,2,149,1"⟩,
  ⟨23, 128, 0, "16,1,167,1"⟩,
  ⟨22, 128, 0, "8,1,218,1"⟩,
  ⟨22, 128, 1, "0,2,64,2"⟩,
  ⟨21, 128, 0, "8,1,219,1"⟩,
  ⟨21, 128, 2, "0,2,299,1"⟩,
  ⟨20, 128, 0, "13,1,194,1"⟩,
  ⟨20, 128, 1, "0,3,292,1"⟩,
  ⟨19, 128, 0, "23,1,150,1"⟩,
  ⟨19, 128, 1, "0,2,301,1"⟩,
  ⟨19, 128, 2, "0,2,300,1"⟩,
  ⟨18, 128, 0, "317,1"⟩,
  ⟨18, 128, 1, "316,1"⟩,
  ⟨18, 128, 3, "0,4,59,1,69,1"⟩,
  ⟨17, 128, 1, "0,2,304,1"⟩,
  ⟨17, 128, 2, "0,2,13,1,188,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2227_mem, Shared.BasisChunk002.row2228_mem, Shared.BasisChunk002.row2229_mem, Shared.BasisChunk002.row2230_mem, Shared.BasisChunk002.row2231_mem, Shared.BasisChunk002.row2232_mem, Shared.BasisChunk002.row2233_mem, Shared.BasisChunk002.row2234_mem, Shared.BasisChunk002.row2235_mem, Shared.BasisChunk002.row2236_mem, Shared.BasisChunk002.row2237_mem, Shared.BasisChunk002.row2238_mem, Shared.BasisChunk002.row2239_mem, Shared.BasisChunk002.row2240_mem, Shared.BasisChunk002.row2241_mem, Shared.BasisChunk002.row2242_mem, Shared.BasisChunk002.row2243_mem, Shared.BasisChunk002.row2244_mem, Shared.BasisChunk002.row2246_mem, Shared.BasisChunk002.row2247_mem, Shared.BasisChunk002.row2248_mem, Shared.BasisChunk002.row2249_mem, Shared.BasisChunk002.row2250_mem, Shared.BasisChunk002.row2251_mem, Shared.BasisChunk002.row2252_mem, Shared.BasisChunk002.row2253_mem, Shared.BasisChunk002.row2255_mem, Shared.BasisChunk002.row2256_mem, Shared.BasisChunk002.row2257_mem, Shared.BasisChunk002.row2259_mem, Shared.BasisChunk002.row2260_mem, Shared.BasisChunk002.row2262_mem, Shared.BasisChunk002.row2263_mem, Shared.BasisChunk002.row2264_mem, Shared.BasisChunk002.row2265_mem, Shared.BasisChunk002.row2266_mem, Shared.BasisChunk002.row2267_mem, Shared.BasisChunk002.row2268_mem, Shared.BasisChunk002.row2269_mem, Shared.BasisChunk002.row2270_mem, Shared.BasisChunk002.row2272_mem, Shared.BasisChunk002.row2273_mem, Shared.BasisChunk002.row2274_mem, Shared.BasisChunk002.row2275_mem, Shared.BasisChunk002.row2276_mem, Shared.BasisChunk002.row2278_mem, Shared.BasisChunk002.row2279_mem, Shared.BasisChunk002.row2280_mem, Shared.BasisChunk002.row2281_mem, Shared.BasisChunk002.row2282_mem, Shared.BasisChunk002.row2283_mem, Shared.BasisChunk002.row2284_mem, Shared.BasisChunk002.row2285_mem, Shared.BasisChunk002.row2287_mem, Shared.BasisChunk002.row2289_mem, Shared.BasisChunk002.row2290_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard029
