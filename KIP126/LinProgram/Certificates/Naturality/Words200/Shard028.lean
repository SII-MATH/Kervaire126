import KIP126.LinProgram.Generated.Naturality.Words200.Shard028
import KIP126.LinProgram.Certificates.Naturality.Words200.Support
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk003
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk006
import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk002

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard028
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard028
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
  exact ⟨Shared.RelationChunk000.relation10_zero, Shared.RelationChunk000.relation18_zero, Shared.RelationChunk000.relation27_zero, Shared.RelationChunk000.relation28_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation119_zero, Shared.RelationChunk000.relation120_zero, Shared.RelationChunk000.relation121_zero, Shared.RelationChunk000.relation122_zero, Shared.RelationChunk000.relation123_zero, Shared.RelationChunk000.relation124_zero, Shared.RelationChunk001.relation143_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation146_zero, Shared.RelationChunk001.relation149_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation194_zero, Shared.RelationChunk001.relation195_zero, Shared.RelationChunk001.relation196_zero, Shared.RelationChunk001.relation199_zero, Shared.RelationChunk001.relation202_zero, Shared.RelationChunk002.relation251_zero, Shared.RelationChunk003.relation278_zero, Shared.RelationChunk003.relation279_zero, Shared.RelationChunk003.relation280_zero, Shared.RelationChunk003.relation281_zero, Shared.RelationChunk003.relation284_zero, Shared.RelationChunk006.relation387_zero, Shared.RelationChunk006.relation389_zero, Shared.RelationChunk006.relation390_zero, Shared.RelationChunk006.relation398_zero, Shared.RelationChunk006.relation400_zero, Shared.RelationChunk006.relation401_zero, Shared.RelationChunk006.relation402_zero, Shared.RelationChunk006.relation403_zero, Shared.RelationChunk006.relation404_zero, Shared.RelationChunk006.relation405_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3586 128 := by cbv
private def targetRows : List BasisRow := [⟨15, 125, 1, "0,1,59,1,69,1"⟩,
  ⟨14, 125, 1, "1,1,287,1"⟩,
  ⟨13, 125, 1, "2,1,275,1"⟩,
  ⟨12, 125, 0, "13,1,181,1"⟩,
  ⟨10, 125, 0, "1,1,289,1"⟩,
  ⟨126, 126, 0, "0,126"⟩,
  ⟨43, 126, 0, "0,2,290,1"⟩,
  ⟨39, 126, 0, "296,1"⟩,
  ⟨35, 126, 0, "8,1,16,1,111,1"⟩,
  ⟨34, 126, 0, "8,1,17,1,111,1"⟩,
  ⟨33, 126, 0, "8,1,211,1"⟩,
  ⟨32, 126, 0, "8,4,49,1"⟩,
  ⟨32, 126, 1, "0,10,245,1"⟩,
  ⟨31, 126, 0, "8,4,50,1"⟩,
  ⟨31, 126, 1, "0,10,246,1"⟩,
  ⟨30, 126, 1, "8,2,16,1,17,2"⟩,
  ⟨29, 126, 0, "298,1"⟩,
  ⟨29, 126, 1, "8,3,88,1"⟩,
  ⟨28, 126, 0, "8,7"⟩,
  ⟨27, 126, 0, "8,5,22,1"⟩,
  ⟨27, 126, 1, "0,4,17,1,149,1"⟩,
  ⟨26, 126, 1, "8,5,23,1"⟩,
  ⟨26, 126, 2, "0,3,17,1,154,1"⟩,
  ⟨25, 126, 0, "8,2,147,1"⟩,
  ⟨25, 126, 1, "8,4,51,1"⟩,
  ⟨25, 126, 2, "0,7,260,1"⟩,
  ⟨24, 126, 0, "8,1,17,1,113,1"⟩,
  ⟨24, 126, 1, "8,3,13,3"⟩,
  ⟨24, 126, 2, "0,5,274,1"⟩,
  ⟨23, 126, 0, "17,1,162,1"⟩,
  ⟨23, 126, 1, "8,2,13,2,32,1"⟩,
  ⟨22, 126, 0, "8,1,13,3,23,1"⟩,
  ⟨22, 126, 1, "8,3,89,1"⟩,
  ⟨21, 126, 0, "13,3,51,1"⟩,
  ⟨21, 126, 1, "8,2,9,1,80,1"⟩,
  ⟨20, 126, 1, "13,3,52,1"⟩,
  ⟨20, 126, 2, "8,1,23,1,89,1"⟩,
  ⟨19, 126, 0, "299,1"⟩,
  ⟨19, 126, 1, "9,1,23,1,80,1"⟩,
  ⟨19, 126, 2, "0,1,291,1"⟩,
  ⟨18, 126, 0, "0,1,292,1"⟩,
  ⟨17, 126, 0, "301,1"⟩,
  ⟨16, 126, 0, "303,1"⟩,
  ⟨16, 126, 3, "0,2,59,1,69,1"⟩,
  ⟨15, 126, 2, "13,1,188,1"⟩,
  ⟨15, 126, 3, "0,1,8,1,209,1"⟩,
  ⟨14, 126, 0, "306,1"⟩,
  ⟨13, 126, 1, "307,1"⟩,
  ⟨12, 126, 0, "309,1"⟩,
  ⟨12, 126, 1, "13,1,190,1"⟩,
  ⟨11, 126, 0, "310,1"⟩,
  ⟨127, 127, 0, "0,127"⟩,
  ⟨41, 127, 0, "0,1,295,1"⟩,
  ⟨40, 127, 0, "0,1,296,1"⟩,
  ⟨37, 127, 0, "0,1,8,2,145,1"⟩,
  ⟨36, 127, 0, "0,1,8,1,16,1,111,1"⟩,
  ⟨33, 127, 0, "0,11,245,1"⟩,
  ⟨32, 127, 1, "0,11,246,1"⟩,
  ⟨31, 127, 0, "0,1,297,1"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk002.row2153_mem, Shared.BasisChunk002.row2155_mem, Shared.BasisChunk002.row2157_mem, Shared.BasisChunk002.row2158_mem, Shared.BasisChunk002.row2159_mem, Shared.BasisChunk002.row2160_mem, Shared.BasisChunk002.row2161_mem, Shared.BasisChunk002.row2163_mem, Shared.BasisChunk002.row2165_mem, Shared.BasisChunk002.row2166_mem, Shared.BasisChunk002.row2167_mem, Shared.BasisChunk002.row2168_mem, Shared.BasisChunk002.row2169_mem, Shared.BasisChunk002.row2170_mem, Shared.BasisChunk002.row2171_mem, Shared.BasisChunk002.row2173_mem, Shared.BasisChunk002.row2174_mem, Shared.BasisChunk002.row2175_mem, Shared.BasisChunk002.row2176_mem, Shared.BasisChunk002.row2177_mem, Shared.BasisChunk002.row2178_mem, Shared.BasisChunk002.row2180_mem, Shared.BasisChunk002.row2181_mem, Shared.BasisChunk002.row2182_mem, Shared.BasisChunk002.row2183_mem, Shared.BasisChunk002.row2184_mem, Shared.BasisChunk002.row2185_mem, Shared.BasisChunk002.row2186_mem, Shared.BasisChunk002.row2187_mem, Shared.BasisChunk002.row2188_mem, Shared.BasisChunk002.row2189_mem, Shared.BasisChunk002.row2190_mem, Shared.BasisChunk002.row2191_mem, Shared.BasisChunk002.row2192_mem, Shared.BasisChunk002.row2193_mem, Shared.BasisChunk002.row2195_mem, Shared.BasisChunk002.row2196_mem, Shared.BasisChunk002.row2197_mem, Shared.BasisChunk002.row2198_mem, Shared.BasisChunk002.row2199_mem, Shared.BasisChunk002.row2200_mem, Shared.BasisChunk002.row2201_mem, Shared.BasisChunk002.row2203_mem, Shared.BasisChunk002.row2206_mem, Shared.BasisChunk002.row2209_mem, Shared.BasisChunk002.row2210_mem, Shared.BasisChunk002.row2211_mem, Shared.BasisChunk002.row2214_mem, Shared.BasisChunk002.row2215_mem, Shared.BasisChunk002.row2216_mem, Shared.BasisChunk002.row2217_mem, Shared.BasisChunk002.row2218_mem, Shared.BasisChunk002.row2219_mem, Shared.BasisChunk002.row2220_mem, Shared.BasisChunk002.row2221_mem, Shared.BasisChunk002.row2222_mem, Shared.BasisChunk002.row2223_mem, Shared.BasisChunk002.row2225_mem, Shared.BasisChunk002.row2226_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard028
