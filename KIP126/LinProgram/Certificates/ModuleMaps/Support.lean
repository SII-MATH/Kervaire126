module

public import KIP126.LinProgram.Certificates.NativeModuleCertificates
public import KIP126.LinProgram.Model.E2.Proofs
public import KIP126.LinProgram.Certificates.RelationCatalogue
public import KIP126.LinProgram.Model.ModulePresentation.Maps

@[expose] public section


open NamedElementCertificates
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates

namespace KIP126.LinModule.NativeMapCertificates

theorem projection_evaluate (p : Polynomial) :
    projection (evaluate nativeVariable p) = evaluate nativeScalar p := by
  simp [evaluate, evaluateMonomial, map_list_sum, map_list_prod,
    List.map_map, Function.comp_def]
  rfl

theorem check_projection_zero (rels : List Polynomial) (input : Polynomial)
    (terms : List Term) (hc : check rels input [] terms = true)
    (hr : ∀ r ∈ rels, evaluate nativeScalar r = 0) :
    evaluate nativeScalar input = 0 := by
  letI : CharP Poly 2 :=
    charP_of_injective_ringHom
      (MvPolynomial.C_injective Generator KIP126.Core.Algebra.F2) 2
  obtain ⟨w, _, hcoeff⟩ := check_sound rels input [] terms hc
  have he := evaluate_coefficients nativeVariable (input ++ []) (combination rels w) hcoeff
  have hp := congrArg projection he
  rw [projection_evaluate, projection_evaluate] at hp
  simpa only [List.append_nil, evaluate_combination nativeScalar rels w hr] using hp

theorem relationPolynomial_words (code : String) :
    relationPolynomial code =
      (((code.splitOn ";").map fun w => if w = "" then [] else
        (w.splitOn ",").map (fun a => a.toNat?.getD 0)).map polynomialOfPowers).sum := by
  simp only [relationPolynomial, List.map_map]
  congr 2
  funext w
  simp only [Function.comp_apply, monomialOfString]
  split <;> simp_all [polynomialOfPowers]

def substituteWord (images : Fin n → Polynomial) : List Nat → Polynomial
  | [j] => if h : j < n then images ⟨j,h⟩ else []
  | i :: a :: rest => if i < RawData.generatorCount then
      multiply [List.replicate a i] (substituteWord images rest) else []
  | _ => []

theorem evaluate_substituteWord (images : Fin n → Polynomial) (word : List Nat) :
    evaluate nativeScalar (substituteWord images word) =
      KIP126.LinModule.Presentation.evaluatePowers
        (fun j => evaluate nativeScalar (images j)) word := by
  induction word using KIP126.LinModule.Presentation.ofPowers.induct n with
  | case1 j hj => simp [substituteWord, KIP126.LinModule.Presentation.evaluatePowers, hj]
  | case2 j hj => simp [substituteWord, KIP126.LinModule.Presentation.evaluatePowers, hj, evaluate]
  | case3 i a rest hi ih =>
      simp only [substituteWord, KIP126.LinModule.Presentation.evaluatePowers,
        dif_pos hi, if_pos hi, evaluate_multiply, ih]
      simp [evaluate, evaluateMonomial, nativeScalar_eq_generator i hi, smul_eq_mul]
  | case4 i a rest hi =>
      simp [substituteWord, KIP126.LinModule.Presentation.evaluatePowers, hi, evaluate]
  | case5 => simp [substituteWord, KIP126.LinModule.Presentation.evaluatePowers, evaluate]

theorem evaluateRelation_words (g : Fin n → E2) (code : String) :
    KIP126.LinModule.Presentation.evaluateRelation g code =
      (((code.splitOn ";").map fun w =>
        (w.splitOn ",").map (fun a => a.toNat?.getD 0)).map
        (KIP126.LinModule.Presentation.evaluatePowers g)).sum := by
  simp only [KIP126.LinModule.Presentation.evaluateRelation, List.map_map,
    Function.comp_def]

def joinRows : List (List Char) → List Char
  | [] => []
  | [r] => r
  | r :: (s :: rows) => r ++ '\n' :: joinRows (s :: rows)

theorem mem_joinRows (rows : List (List Char))
    (hn : ∀ row ∈ rows, '\n' ∉ row) (row : List Char) (hr : row ∈ rows) :
    row ∈ (joinRows rows).splitOn '\n' := by
  induction rows using joinRows.induct with
  | case1 => simp at hr
  | case2 r =>
    have he : row = r := by simpa using hr
    subst row
    simp only [joinRows, List.splitOn_eq_singleton (hn r (by simp)), List.mem_singleton]
  | case3 r s rows ih =>
    rw [joinRows, List.splitOn_append_cons_self,
      List.splitOn_eq_singleton (hn r (by simp))]
    simp only [List.singleton_append, List.mem_cons] at *
    rcases hr with rfl | hr
    · exact Or.inl rfl
    · exact Or.inr (ih (fun w hw => hn w (Or.inr hw)) hr)

theorem rawChunk_mem (i : Nat) (hi : i < RawData.relationChunks.size)
    (rows : List (List Char))
    (hc : RawData.relationChunks[i] = String.ofList (joinRows rows))
    (hn : ∀ row ∈ rows, '\n' ∉ row) (row : List Char) (hr : row ∈ rows) :
    String.ofList row ∈ RawData.relations := by
  apply RelationCatalogue.rawLine_mem_of_chars i hi row
  rw [hc, String.toList_ofList]
  exact mem_joinRows rows hn row hr

/-- The native image convention is explicit: the empty graph entry is zero. -/
noncomputable def nativeImage (code : String) : E2 :=
  if code = "" then 0 else projection (relationPolynomial code)

def parsePowers : List Nat → Polynomial
  | [] => [[]]
  | i :: a :: rest => if i < RawData.generatorCount then
      multiply [List.replicate a i] (parsePowers rest) else []
  | [_] => []

def parseMonomial (code : String) : Polynomial :=
  if code = "" then [[]] else parsePowers ((code.splitOn ",").map (fun a => a.toNat?.getD 0))

def parseNativeCode (code : String) : Polynomial :=
  if code = "" then [] else (code.splitOn ";").flatMap parseMonomial

theorem evaluate_parsePowers (word : List Nat) :
    evaluate nativeVariable (parsePowers word) = polynomialOfPowers word := by
  induction word using polynomialOfPowers.induct with
  | case1 => simp [parsePowers, polynomialOfPowers, evaluate, evaluateMonomial]
  | case2 i a rest hi ih =>
    simp only [parsePowers, polynomialOfPowers, if_pos hi, dif_pos hi,
      evaluate_multiply, ih]
    simp [evaluate, evaluateMonomial, nativeVariable, hi]
  | case3 i a rest hi =>
    simp [parsePowers, polynomialOfPowers, hi, evaluate]
  | case4 i => simp [parsePowers, polynomialOfPowers, evaluate]

theorem evaluate_flatMap {R : Type*} [CommRing R] (v : Nat → R)
    (codes : List α) (f : α → Polynomial) :
    evaluate v (codes.flatMap f) = (codes.map (fun code => evaluate v (f code))).sum := by
  induction codes with
  | nil => rfl
  | cons code codes ih => simp only [List.flatMap_cons, evaluate_append, ih,
      List.map_cons, List.sum_cons]

theorem evaluate_parseMonomial (code : String) :
    evaluate nativeVariable (parseMonomial code) = monomialOfString code := by
  by_cases h : code = ""
  · simp [parseMonomial, monomialOfString, h, evaluate, evaluateMonomial]
  · simp only [parseMonomial, monomialOfString, if_neg h, evaluate_parsePowers]

/-- Parser correctness for every string; no validity, degree or nontriviality
hypothesis is hidden in the native generator-image binding. -/
theorem evaluate_parseNativeCode (code : String) :
    evaluate nativeScalar (parseNativeCode code) = nativeImage code := by
  by_cases h : code = ""
  · simp [parseNativeCode, nativeImage, h, evaluate]
  · rw [← projection_evaluate]
    simp only [parseNativeCode, nativeImage, if_neg h, evaluate_flatMap,
      evaluate_parseMonomial, relationPolynomial]

end KIP126.LinModule.NativeMapCertificates
