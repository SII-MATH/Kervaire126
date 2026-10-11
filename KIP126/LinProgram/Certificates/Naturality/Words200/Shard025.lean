module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Generated.Naturality.Words200.Shard025
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk000
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk001
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk002
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.RelationChunk005
public import KIP126.LinProgram.Certificates.Naturality.Words200.Shared.BasisChunk001

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shard025
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open KIP126.LinModule.RawData.NaturalityWords200.Shard025
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
  exact ⟨Shared.RelationChunk000.relation24_zero, Shared.RelationChunk000.relation63_zero, Shared.RelationChunk000.relation64_zero, Shared.RelationChunk000.relation69_zero, Shared.RelationChunk000.relation70_zero, Shared.RelationChunk000.relation78_zero, Shared.RelationChunk000.relation79_zero, Shared.RelationChunk000.relation85_zero, Shared.RelationChunk000.relation86_zero, Shared.RelationChunk000.relation87_zero, Shared.RelationChunk000.relation117_zero, Shared.RelationChunk001.relation144_zero, Shared.RelationChunk001.relation167_zero, Shared.RelationChunk001.relation168_zero, Shared.RelationChunk001.relation170_zero, Shared.RelationChunk001.relation190_zero, Shared.RelationChunk002.relation226_zero, Shared.RelationChunk002.relation250_zero, Shared.RelationChunk005.relation345_zero, Shared.RelationChunk005.relation346_zero, Shared.RelationChunk005.relation350_zero, Shared.RelationChunk005.relation351_zero, Shared.RelationChunk005.relation358_zero, Shared.RelationChunk005.relation359_zero, Shared.RelationChunk005.relation360_zero, Shared.RelationChunk005.relation361_zero, by simp⟩
theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv
theorem source_ids : entries.map (fun e => e.source.id) = List.range' 3202 128 := by cbv
private def targetRows : List BasisRow := [⟨25, 120, 2, "0,1,257,1"⟩,
  ⟨25, 120, 3, "0,4,246,1"⟩,
  ⟨24, 120, 0, "17,1,147,1"⟩,
  ⟨24, 120, 1, "8,4,13,2"⟩,
  ⟨23, 120, 0, "8,3,13,1,32,1"⟩,
  ⟨23, 120, 1, "0,1,258,1"⟩,
  ⟨22, 120, 0, "8,2,13,2,23,1"⟩,
  ⟨22, 120, 1, "8,3,72,1"⟩,
  ⟨21, 120, 0, "8,1,13,2,51,1"⟩,
  ⟨21, 120, 1, "8,2,127,1"⟩,
  ⟨20, 120, 0, "13,5"⟩,
  ⟨20, 120, 1, "8,1,20,1,80,1"⟩,
  ⟨19, 120, 0, "13,2,23,1,24,1"⟩,
  ⟨19, 120, 1, "8,1,186,1"⟩,
  ⟨19, 120, 2, "0,1,260,1"⟩,
  ⟨18, 120, 0, "9,1,13,1,101,1"⟩,
  ⟨18, 120, 1, "0,2,50,1,69,1"⟩,
  ⟨15, 120, 1, "8,1,188,1"⟩,
  ⟨14, 120, 0, "267,1"⟩,
  ⟨14, 120, 1, "0,2,7,1,188,1"⟩,
  ⟨13, 120, 0, "268,1"⟩,
  ⟨10, 120, 1, "3,2,197,1"⟩,
  ⟨10, 120, 2, "2,1,251,1"⟩,
  ⟨9, 120, 0, "271,1"⟩,
  ⟨9, 120, 2, "3,2,198,1"⟩,
  ⟨9, 120, 3, "0,1,53,1,69,1"⟩,
  ⟨8, 120, 0, "272,1"⟩,
  ⟨8, 120, 1, "3,1,230,1"⟩,
  ⟨8, 120, 2, "0,1,264,1"⟩,
  ⟨7, 120, 0, "54,1,69,1"⟩,
  ⟨7, 120, 1, "3,1,231,1"⟩,
  ⟨6, 120, 0, "273,1"⟩,
  ⟨121, 121, 0, "0,121"⟩,
  ⟨40, 121, 0, "1,1,256,1"⟩,
  ⟨37, 121, 0, "0,1,8,1,182,1"⟩,
  ⟨36, 121, 0, "0,1,8,1,183,1"⟩,
  ⟨29, 121, 0, "0,5,244,1"⟩,
  ⟨28, 121, 0, "0,4,17,1,138,1"⟩,
  ⟨27, 121, 0, "0,1,8,1,184,1"⟩,
  ⟨27, 121, 1, "0,5,245,1"⟩,
  ⟨26, 121, 0, "0,1,8,1,185,1"⟩,
  ⟨26, 121, 1, "0,2,257,1"⟩,
  ⟨26, 121, 2, "0,5,246,1"⟩,
  ⟨25, 121, 0, "0,1,17,1,147,1"⟩,
  ⟨20, 121, 0, "0,2,260,1"⟩,
  ⟨19, 121, 0, "274,1"⟩,
  ⟨17, 121, 1, "0,1,8,1,187,1"⟩,
  ⟨16, 121, 0, "56,1,69,1"⟩,
  ⟨16, 121, 1, "0,1,266,1"⟩,
  ⟨16, 121, 2, "0,1,8,1,188,1"⟩,
  ⟨15, 121, 0, "13,2,95,1"⟩,
  ⟨15, 121, 2, "0,1,267,1"⟩,
  ⟨14, 121, 0, "13,1,164,1"⟩,
  ⟨13, 121, 0, "1,1,261,1"⟩,
  ⟨12, 121, 1, "8,1,29,1,69,1"⟩,
  ⟨11, 121, 0, "0,1,3,2,197,1"⟩,
  ⟨11, 121, 1, "0,1,2,1,251,1"⟩,
  ⟨10, 121, 0, "0,1,270,1"⟩,
  ⟨10, 121, 1, "0,2,53,1,69,1"⟩,
  ⟨6, 121, 0, "57,1,69,1"⟩,
  ⟨122, 122, 0, "0,122"⟩]
private theorem targetRows_mem : ∀ r ∈ targetRows, r ∈ basisRows := by
  simp only [targetRows, List.forall_mem_cons]
  exact ⟨Shared.BasisChunk001.row1934_mem, Shared.BasisChunk001.row1935_mem, Shared.BasisChunk001.row1936_mem, Shared.BasisChunk001.row1937_mem, Shared.BasisChunk001.row1938_mem, Shared.BasisChunk001.row1939_mem, Shared.BasisChunk001.row1940_mem, Shared.BasisChunk001.row1941_mem, Shared.BasisChunk001.row1942_mem, Shared.BasisChunk001.row1943_mem, Shared.BasisChunk001.row1944_mem, Shared.BasisChunk001.row1945_mem, Shared.BasisChunk001.row1946_mem, Shared.BasisChunk001.row1947_mem, Shared.BasisChunk001.row1948_mem, Shared.BasisChunk001.row1949_mem, Shared.BasisChunk001.row1950_mem, Shared.BasisChunk001.row1953_mem, Shared.BasisChunk001.row1954_mem, Shared.BasisChunk001.row1955_mem, Shared.BasisChunk001.row1956_mem, Shared.BasisChunk001.row1958_mem, Shared.BasisChunk001.row1959_mem, Shared.BasisChunk001.row1960_mem, Shared.BasisChunk001.row1962_mem, Shared.BasisChunk001.row1963_mem, Shared.BasisChunk001.row1964_mem, Shared.BasisChunk001.row1965_mem, Shared.BasisChunk001.row1966_mem, Shared.BasisChunk001.row1967_mem, Shared.BasisChunk001.row1968_mem, Shared.BasisChunk001.row1969_mem, Shared.BasisChunk001.row1970_mem, Shared.BasisChunk001.row1971_mem, Shared.BasisChunk001.row1972_mem, Shared.BasisChunk001.row1973_mem, Shared.BasisChunk001.row1974_mem, Shared.BasisChunk001.row1975_mem, Shared.BasisChunk001.row1976_mem, Shared.BasisChunk001.row1977_mem, Shared.BasisChunk001.row1978_mem, Shared.BasisChunk001.row1979_mem, Shared.BasisChunk001.row1980_mem, Shared.BasisChunk001.row1981_mem, Shared.BasisChunk001.row1982_mem, Shared.BasisChunk001.row1983_mem, Shared.BasisChunk001.row1986_mem, Shared.BasisChunk001.row1987_mem, Shared.BasisChunk001.row1988_mem, Shared.BasisChunk001.row1989_mem, Shared.BasisChunk001.row1990_mem, Shared.BasisChunk001.row1992_mem, Shared.BasisChunk001.row1993_mem, Shared.BasisChunk001.row1994_mem, Shared.BasisChunk001.row1996_mem, Shared.BasisChunk001.row1997_mem, Shared.BasisChunk001.row1998_mem, Shared.BasisChunk001.row1999_mem, Shared.BasisChunk001.row2000_mem, Shared.BasisChunk001.row2001_mem, Shared.BasisChunk001.row2002_mem, by simp⟩
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
end KIP126.LinModule.NaturalityWords200.Shard025
