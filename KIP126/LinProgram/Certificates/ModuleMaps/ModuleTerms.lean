module

public import KIP126.LinProgram.Certificates.ModuleMaps.ModuleSupport
public import KIP126.LinProgram.Model.ModulePresentation.Maps

@[expose] public section


namespace KIP126.LinE2.NativeModuleCertificates.Support
open NamedElementCertificates
open KIP126.LinModule
noncomputable section

abbrev ModuleTerms (n : Nat) := List (Fin n × Polynomial)

def termsExpression : ModuleTerms n → ModuleExpressions.Expression n
  | [] => ModuleExpressions.zero
  | (j, p) :: ts => ModuleExpressions.add (slot j p) (termsExpression ts)

def scaleTerms (p : Polynomial) (ts : ModuleTerms n) : ModuleTerms n :=
  ts.map fun t => (t.1, NamedElementCertificates.multiply p t.2)

theorem evaluate_termsExpression_append {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (v : Nat → R) (g : Fin n → M) (a b : ModuleTerms n) :
    ModuleExpressions.evaluate v g (termsExpression (a ++ b)) =
      ModuleExpressions.evaluate v g (termsExpression a) +
      ModuleExpressions.evaluate v g (termsExpression b) := by
  induction a with
  | nil => simp only [List.nil_append, termsExpression, ModuleExpressions.evaluate_zero, zero_add]
  | cons t ts ih =>
    rcases t with ⟨j,p⟩
    simp only [List.cons_append, termsExpression, ModuleExpressions.evaluate_add, ih, add_assoc]

theorem evaluate_scaleTerms {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : Nat → R) (g : Fin n → M) (p : Polynomial) (ts : ModuleTerms n) :
    ModuleExpressions.evaluate v g (termsExpression (scaleTerms p ts)) =
      NamedElementCertificates.evaluate v p • ModuleExpressions.evaluate v g (termsExpression ts) := by
  induction ts with
  | nil => simp [scaleTerms, termsExpression, ModuleExpressions.evaluate_zero]
  | cons t ts ih =>
    rcases t with ⟨j,q⟩
    simp only [scaleTerms, List.map_cons, termsExpression, ModuleExpressions.evaluate_add,
      evaluate_slot, evaluate_multiply, mul_smul, smul_add] at *
    rw [ih]

def substituteModuleWord (images : Fin n → ModuleTerms m) : List Nat → ModuleTerms m
  | [j] => if h : j < n then images ⟨j,h⟩ else []
  | i :: a :: rest => if i < RawData.generatorCount then
      scaleTerms [List.replicate a i] (substituteModuleWord images rest) else []
  | _ => []

theorem evaluate_substituteModuleWord {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin m → M) (images : Fin n → ModuleTerms m) (word : List Nat) :
    ModuleExpressions.evaluate nativeScalar g (termsExpression (substituteModuleWord images word)) =
      Presentation.evaluatePowers
        (fun j => ModuleExpressions.evaluate nativeScalar g (termsExpression (images j))) word := by
  induction word using Presentation.ofPowers.induct n with
  | case1 j hj => simp [substituteModuleWord, Presentation.evaluatePowers, hj]
  | case2 j hj => simp [substituteModuleWord, Presentation.evaluatePowers, hj,
      termsExpression, ModuleExpressions.evaluate_zero]
  | case3 i a rest hi ih =>
      simp only [substituteModuleWord, Presentation.evaluatePowers, dif_pos hi, if_pos hi,
        evaluate_scaleTerms, ih]
      simp [NamedElementCertificates.evaluate, evaluateMonomial, nativeScalar_eq_generator i hi]
  | case4 i a rest hi => simp [substituteModuleWord, Presentation.evaluatePowers, hi,
      termsExpression, ModuleExpressions.evaluate_zero]
  | case5 => simp [substituteModuleWord, Presentation.evaluatePowers,
      termsExpression, ModuleExpressions.evaluate_zero]

def substituteModuleRelation (images : Fin n → ModuleTerms m) (code : String) : ModuleTerms m :=
  (code.splitOn ";").flatMap fun w =>
    substituteModuleWord images ((w.splitOn ",").map (fun a => a.toNat?.getD 0))

theorem substituteModuleRelation_words (images : Fin n → ModuleTerms m) (code : String) :
    substituteModuleRelation images code =
      (((code.splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)).flatMap
        (substituteModuleWord images)) := by
  simp only [substituteModuleRelation, List.flatMap_map]

theorem evaluate_terms_flatMap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : Nat → R) (g : Fin n → M) (xs : List α) (f : α → ModuleTerms n) :
    ModuleExpressions.evaluate v g (termsExpression (xs.flatMap f)) =
      (xs.map fun x => ModuleExpressions.evaluate v g (termsExpression (f x))).sum := by
  induction xs with
  | nil => simp [termsExpression, ModuleExpressions.evaluate_zero]
  | cons x xs ih => simp only [List.flatMap_cons, evaluate_termsExpression_append,
      ih, List.map_cons, List.sum_cons]

theorem evaluate_substituteModuleRelation {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin m → M) (images : Fin n → ModuleTerms m) (code : String) :
    ModuleExpressions.evaluate nativeScalar g (termsExpression (substituteModuleRelation images code)) =
      Presentation.evaluateRelation
        (fun j => ModuleExpressions.evaluate nativeScalar g (termsExpression (images j))) code := by
  simp only [substituteModuleRelation, evaluate_terms_flatMap,
    evaluate_substituteModuleWord, Presentation.evaluateRelation]

def moduleRelationTerms (n : Nat) (code : String) : ModuleTerms n :=
  substituteModuleRelation (fun j => [(j, [[]])]) code

def nativeModuleTerms (n : Nat) (code : String) : ModuleTerms n :=
  if code = "" then [] else moduleRelationTerms n code

theorem evaluate_moduleRelationTerms (n : Nat) (rels : List String) (code : String) :
    ModuleExpressions.evaluate nativeScalar (Presentation.generator n rels)
      (termsExpression (moduleRelationTerms n code)) =
      Presentation.projection n rels (Presentation.relationVector n code) := by
  rw [moduleRelationTerms, evaluate_substituteModuleRelation, projection_relation_words]
  simp only [termsExpression, ModuleExpressions.evaluate_add, evaluate_slot,
    ModuleExpressions.evaluate_zero, add_zero, NamedElementCertificates.evaluate,
    evaluateMonomial, List.map_cons, List.map_nil, List.prod_nil, List.sum_cons,
    List.sum_nil, one_smul, Presentation.evaluateRelation, List.map_map, Function.comp_def]

theorem evaluate_nativeModuleTerms (n : Nat) (rels : List String) (code : String) :
    ModuleExpressions.evaluate nativeScalar (Presentation.generator n rels)
      (termsExpression (nativeModuleTerms n code)) = nativeModuleImage n rels code := by
  by_cases h : code = ""
  · simp [nativeModuleTerms, nativeModuleImage, h, termsExpression, ModuleExpressions.evaluate_zero]
  · simp only [nativeModuleTerms, nativeModuleImage, if_neg h, evaluate_moduleRelationTerms]

/-- The support condition checks every term; it does not assume a finite-rank
quotient or require vanishing of omitted original target generators. -/
theorem termsExpression_off_support (e : Fin k ↪ Fin n) (ts : ModuleTerms n)
    (hs : ∀ t ∈ ts, t.1 ∈ Set.range e) (j : Fin n) (hj : j ∉ Set.range e) :
    termsExpression ts j = [] := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨i,p⟩
    have hi : j ≠ i := by intro h; subst j; exact hj (hs (i,p) (by simp))
    simp only [termsExpression, ModuleExpressions.add, slot, if_neg hi, List.nil_append]
    exact ih (fun t ht => hs t (List.mem_cons_of_mem _ ht))

theorem evaluate_restrict_terms {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : Nat → R) (g : Fin n → M) (e : Fin k ↪ Fin n) (ts : ModuleTerms n)
    (hs : ∀ t ∈ ts, t.1 ∈ Set.range e) :
    ModuleExpressions.evaluate v (g ∘ e) (restrict e (termsExpression ts)) =
      ModuleExpressions.evaluate v g (termsExpression ts) :=
  evaluate_restrict v g e _ (termsExpression_off_support e ts hs)

def termsSupported (e : Fin k ↪ Fin n) (ts : ModuleTerms n) : Bool :=
  ts.all fun t => decide (∃ i, e i = t.1)

theorem termsSupported_spec (e : Fin k ↪ Fin n) (ts : ModuleTerms n)
    (h : termsSupported e ts = true) : ∀ t ∈ ts, t.1 ∈ Set.range e := by
  simpa only [termsSupported, List.all_eq_true, decide_eq_true_eq, Set.mem_range] using h

/-- An optimization of the unchanged checker, with a decidable support
certificate for every full-target relation and input term. -/
theorem check_terms_projection_zero {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin n → M) (e : Fin k ↪ Fin n) (rels : List (ModuleTerms n))
    (input : ModuleTerms n) (terms : List Term)
    (hs : (input :: rels).all (termsSupported e) = true)
    (hc : ModuleExpressions.check
      (rels.map fun ts => restrict e (termsExpression ts))
      (restrict e (termsExpression input)) ModuleExpressions.zero terms = true)
    (hr : ∀ ts ∈ rels, ModuleExpressions.evaluate nativeScalar g (termsExpression ts) = 0) :
    ModuleExpressions.evaluate nativeScalar g (termsExpression input) = 0 := by
  have hs' : ∀ ts ∈ input :: rels, ∀ t ∈ ts, t.1 ∈ Set.range e := by
    intro ts hts
    exact termsSupported_spec e ts ((List.all_eq_true.mp hs) ts hts)
  rw [← evaluate_restrict_terms nativeScalar g e input (hs' input (by simp))]
  have hh := check_sound_projection nativeVariable (g ∘ e)
    (rels.map fun ts => restrict e (termsExpression ts))
    (restrict e (termsExpression input)) ModuleExpressions.zero terms hc (by
      intro r hr'
      obtain ⟨ts, hts, rfl⟩ := List.mem_map.mp hr'
      change ModuleExpressions.evaluate nativeScalar (g ∘ e) (restrict e (termsExpression ts)) = 0
      rw [evaluate_restrict_terms nativeScalar g e ts (hs' ts (by simp [hts]))]
      exact hr ts hts)
  exact hh.trans (ModuleExpressions.evaluate_zero nativeScalar (g ∘ e))

theorem evaluate_single_terms_zero {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin n → M) (j : Fin n) (p : Polynomial)
    (hp : NamedElementCertificates.evaluate nativeScalar p = 0) :
    ModuleExpressions.evaluate nativeScalar g (termsExpression [(j,p)]) = 0 := by
  simp only [termsExpression, ModuleExpressions.evaluate_add, evaluate_slot,
    ModuleExpressions.evaluate_zero, hp, add_zero]
  exact zero_smul E2 (g j)

end
end KIP126.LinE2.NativeModuleCertificates.Support
