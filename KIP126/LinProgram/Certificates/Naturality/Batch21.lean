import KIP126.LinProgram.Generated.Naturality.Batch21
import KIP126.LinProgram.Certificates.BasisCatalogue.Archive
import KIP126.LinProgram.Tactic.LinRelation

/-! Checked map evaluations for every exported Ceta basis row with 2 ≤ t ≤ 21.
Coverage of the original Ceta table is checked during deterministic export;
Lean checks all 82 evaluations, the one used sphere relation, and every target
row's membership in the original sphere catalogue. These facts do not assert
that the catalogues are mathematical bases or identify an actual spectrum map. -/
namespace KIP126.LinModule.NaturalityBatch21
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)
open RawData.NaturalityBatch21

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe

/-- This is an original relation of the unchanged sphere quotient. -/
theorem relation_mem : "2,3;1,2,3,1" ∈ LinE2.RawData.relations := by
  lin_relation 0 "2,3;1,2,3,1"

theorem relations_zero : ∀ code ∈ relationCodes, nativeImage code = 0 := by
  intro code hcode
  have hc : code = "2,3;1,2,3,1" := by simpa [relationCodes] using hcode
  subst code
  change projection (relationPolynomial "2,3;1,2,3,1") = 0
  exact csv_relation_zero _ relation_mem

theorem all_checks : entries.all (BatchMapCertificate.check relationCodes) = true := by cbv

theorem entry_count : entries.length = 82 := by cbv

theorem zero_count : (entries.filter (fun e => e.targets.isEmpty)).length = 45 := by cbv

/-- A singleton coordinate list does not assert that its class is nonzero. -/
theorem singleton_count : (entries.filter (fun e => e.targets.length == 1)).length = 37 := by cbv

theorem relation_witness_count :
    (entries.filter (fun e => !e.witness.isEmpty)).length = 1 := by cbv

/-- Every exported row gets a closed equation in the existing sphere quotient. -/
theorem entry_evaluate (e : Entry) (he : e ∈ entries) :
    Presentation.evaluatePowers generatorImage (word e) = targetValue e :=
  BatchMapCertificate.check_sound relationCodes e
    ((List.all_eq_true.mp all_checks) e he) relations_zero

theorem zero_evaluate (e : Entry) (he : e ∈ entries) (hz : e.targets = []) :
    Presentation.evaluatePowers generatorImage (word e) = 0 := by
  rw [entry_evaluate e he]
  simp only [targetValue, hz, List.map_nil, List.sum_nil]

/-- The whole-batch descent theorem retains every original Ceta relation. -/
theorem entry_desc (e : Entry) (he : e ∈ entries)
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Ceta.monomial e.source.code) = targetValue e :=
  BatchMapCertificate.check_sound_desc relationCodes e
    ((List.all_eq_true.mp all_checks) e he) relations_zero hrel

/-- A finite list of candidate target rows, each independently bound below to
the unchanged complete catalogue. It is not a replacement mathematical basis. -/
def targetCatalogueRows : List BasisRow := [
  ⟨1, 1, 0, "0,1"⟩,
  ⟨2, 2, 0, "0,2"⟩,
  ⟨3, 3, 0, "0,3"⟩,
  ⟨4, 4, 0, "0,4"⟩,
  ⟨1, 4, 0, "2,1"⟩,
  ⟨5, 5, 0, "0,5"⟩,
  ⟨2, 5, 0, "0,1,2,1"⟩,
  ⟨6, 6, 0, "0,6"⟩,
  ⟨3, 6, 0, "0,2,2,1"⟩,
  ⟨7, 7, 0, "0,7"⟩,
  ⟨8, 8, 0, "0,8"⟩,
  ⟨2, 8, 0, "2,2"⟩,
  ⟨9, 9, 0, "0,9"⟩,
  ⟨2, 9, 0, "0,1,3,1"⟩,
  ⟨10, 10, 0, "0,10"⟩,
  ⟨3, 10, 0, "0,2,3,1"⟩,
  ⟨11, 11, 0, "0,11"⟩,
  ⟨4, 11, 0, "0,3,3,1"⟩,
  ⟨12, 12, 0, "0,12"⟩,
  ⟨3, 12, 0, "1,2,3,1"⟩,
  ⟨13, 13, 0, "0,13"⟩,
  ⟨4, 13, 0, "1,1,4,1"⟩,
  ⟨14, 14, 0, "0,14"⟩,
  ⟨15, 15, 0, "0,15"⟩,
  ⟨16, 16, 0, "0,16"⟩,
  ⟨5, 16, 0, "6,1"⟩,
  ⟨2, 16, 0, "3,2"⟩,
  ⟨17, 17, 0, "0,17"⟩,
  ⟨6, 17, 0, "0,1,6,1"⟩,
  ⟨3, 17, 0, "0,1,3,2"⟩,
  ⟨2, 17, 0, "0,1,7,1"⟩,
  ⟨18, 18, 0, "0,18"⟩,
  ⟨7, 18, 0, "0,2,6,1"⟩,
  ⟨3, 18, 0, "0,2,7,1"⟩,
  ⟨19, 19, 0, "0,19"⟩,
  ⟨5, 19, 0, "0,1,8,1"⟩,
  ⟨4, 19, 0, "0,3,7,1"⟩]

/-- The first 100 archived lines are a witness, checked once against the full
original chunk. All selected targets lie in this prefix. -/
private def archivedPrefixLines : List String := ["0|0|0|",
  "1|1|0|0,1",
  "2|2|0|0,2",
  "1|2|0|1,1",
  "3|3|0|0,3",
  "4|4|0|0,4",
  "2|4|0|1,2",
  "1|4|0|2,1",
  "5|5|0|0,5",
  "2|5|0|0,1,2,1",
  "6|6|0|0,6",
  "3|6|0|0,2,2,1",
  "7|7|0|0,7",
  "8|8|0|0,8",
  "2|8|0|2,2",
  "1|8|0|3,1",
  "9|9|0|0,9",
  "2|9|0|0,1,3,1",
  "10|10|0|0,10",
  "3|10|0|0,2,3,1",
  "2|10|0|1,1,3,1",
  "11|11|0|0,11",
  "4|11|0|0,3,3,1",
  "3|11|0|4,1",
  "12|12|0|0,12",
  "3|12|0|1,2,3,1",
  "13|13|0|0,13",
  "4|13|0|1,1,4,1",
  "14|14|0|0,14",
  "5|14|0|5,1",
  "15|15|0|0,15",
  "16|16|0|0,16",
  "6|16|0|1,1,5,1",
  "5|16|0|6,1",
  "2|16|0|3,2",
  "1|16|0|7,1",
  "17|17|0|0,17",
  "6|17|0|0,1,6,1",
  "3|17|0|0,1,3,2",
  "2|17|0|0,1,7,1",
  "18|18|0|0,18",
  "7|18|0|0,2,6,1",
  "4|18|0|8,1",
  "3|18|0|0,2,7,1",
  "2|18|0|1,1,7,1",
  "19|19|0|0,19",
  "5|19|0|0,1,8,1",
  "4|19|0|0,3,7,1",
  "20|20|0|0,20",
  "6|20|0|0,2,8,1",
  "5|20|0|1,1,8,1",
  "5|20|1|0,4,7,1",
  "3|20|0|1,2,7,1",
  "2|20|0|2,1,7,1",
  "21|21|0|0,21",
  "6|21|0|0,5,7,1",
  "4|21|0|9,1",
  "3|21|0|0,1,2,1,7,1",
  "22|22|0|0,22",
  "7|22|0|0,6,7,1",
  "6|22|0|1,2,8,1",
  "5|22|0|0,1,9,1",
  "4|22|0|10,1",
  "4|22|1|0,2,2,1,7,1",
  "3|22|0|11,1",
  "23|23|0|0,23",
  "8|23|0|0,7,7,1",
  "7|23|0|12,1",
  "6|23|0|0,2,9,1",
  "5|23|0|0,1,10,1",
  "24|24|0|0,24",
  "7|24|0|0,3,9,1",
  "4|24|0|13,1",
  "3|24|0|2,2,7,1",
  "25|25|0|0,25",
  "8|25|0|1,1,12,1",
  "5|25|0|0,1,13,1",
  "26|26|0|0,26",
  "9|26|0|14,1",
  "6|26|0|0,2,13,1",
  "5|26|0|1,1,13,1",
  "4|26|0|2,1,11,1",
  "27|27|0|0,27",
  "4|27|0|4,1,7,1",
  "28|28|0|0,28",
  "10|28|0|1,1,14,1",
  "9|28|0|15,1",
  "5|28|0|2,1,13,1",
  "29|29|0|0,29",
  "10|29|0|0,1,15,1",
  "6|29|0|0,1,2,1,13,1",
  "5|29|0|1,1,4,1,7,1",
  "30|30|0|0,30",
  "11|30|0|0,2,15,1",
  "8|30|0|16,1",
  "7|30|0|17,1",
  "31|31|0|0,31",
  "9|31|0|0,1,16,1",
  "8|31|0|0,1,17,1",
  "32|32|0|0,32"]

/- Runtime extraction only proposes character witnesses. The equality with
the original archived chunk is checked below by the kernel, just as in the
existing `lin_basis_line` tactic. Expanded characters avoid expensive repeated
kernel decoding of the long suffix. -/
open Lean Elab Tactic in
private def archivedPrefixChars : List (List Char) := by
  run_tac
    let rows := (LinE2.RawData.basisChunks[0]!).splitOn "\n"
    (← getMainGoal).assign (toExpr ((rows.take 100).map String.toList))
    replaceMainGoal []

open Lean Elab Tactic in
private def archivedSuffixChars : List Char := by
  run_tac
    let rows := (LinE2.RawData.basisChunks[0]!).splitOn "\n"
    (← getMainGoal).assign (toExpr (String.intercalate "\n" (rows.drop 100)).toList)
    replaceMainGoal []

private theorem prefix_decomposition :
    LinE2.RawData.basisChunks[0]'(by decide) = String.ofList
      (joinRows archivedPrefixChars ++ '\n' :: archivedSuffixChars) := by rfl

private theorem prefix_chars : archivedPrefixChars =
    archivedPrefixLines.map String.toList := by cbv

private theorem prefix_noNewline :
    ∀ cs ∈ archivedPrefixChars, '\n' ∉ cs := by decide +kernel

private theorem prefixLine_mem (line : String) (hl : line ∈ archivedPrefixLines) :
    line ∈ LinE2.RawData.basisChunks.toList.flatMap (·.splitOn "\n") := by
  apply List.mem_flatMap.mpr
  refine ⟨LinE2.RawData.basisChunks[0]'(by decide), Array.getElem_mem_toList (by decide), ?_⟩
  rw [SquareDetection.splitOn_newline, prefix_decomposition, String.toList_ofList,
    List.splitOn_append_cons_self]
  have hm : line.toList ∈ (joinRows archivedPrefixChars).splitOn '\n' :=
    mem_joinRows _ prefix_noNewline _ (by
      rw [prefix_chars]
      exact List.mem_map.mpr ⟨line, hl, rfl⟩)
  simpa only [String.ofList_toList] using
    List.mem_map_of_mem (f := String.ofList) (List.mem_append_left _ hm)

private def rowLine (r : BasisRow) : String :=
  toString r.s ++ "|" ++ toString r.t ++ "|" ++ toString r.index ++ "|" ++ r.monomial

private theorem targetRows_bound : targetCatalogueRows.all (fun r =>
    archivedPrefixLines.contains (rowLine r) &&
      decide (decodeBasisRow (rowLine r) = .ok r)) = true := by cbv

theorem targetCatalogueRows_mem (r : BasisRow) (hr : r ∈ targetCatalogueRows) :
    r ∈ basisRows := by
  have h := (List.all_eq_true.mp targetRows_bound) r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid (rowLine r)
    (prefixLine_mem _ (by simpa using h.1)) r h.2

/-- Membership is checked against this finite list only after all its rows
have been proved to belong to the original complete catalogue. -/
def catalogueCheck (r : BasisRecord) : Bool :=
  targetCatalogueRows.any (fun row => decide
    (row.s = r.s ∧ row.t = r.t ∧ row.index = r.localIndex ∧ row.monomial = r.code))

theorem catalogueCheck_sound (r : BasisRecord) (hc : catalogueCheck r = true) :
    basisRow r ∈ basisRows := by
  obtain ⟨row, hr, h⟩ := List.any_eq_true.mp hc
  simp only [decide_eq_true_eq] at h
  have heq : row = basisRow r := by
    cases row
    cases r
    simp_all [basisRow]
  rw [← heq]
  exact targetCatalogueRows_mem row hr

theorem all_target_catalogue_checks :
    entries.all (fun e => e.targets.all catalogueCheck) = true := by cbv

/-- Every coordinate used on every right-hand side belongs to the full archived
sphere catalogue; no newly invented target list is accepted as its own basis. -/
theorem target_row_mem (e : Entry) (he : e ∈ entries)
    (r : BasisRecord) (hr : r ∈ e.targets) : basisRow r ∈ basisRows :=
  catalogueCheck_sound r
    ((List.all_eq_true.mp ((List.all_eq_true.mp all_target_catalogue_checks) e he)) r hr)

end KIP126.LinModule.NaturalityBatch21
