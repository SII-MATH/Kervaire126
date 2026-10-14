module

public import KIP126.LinProgram.Certificates.NamedElements.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section


namespace NamedElementCertificates
open scoped BigOperators

variable {R : Type*} [CommRing R]

def evaluateMonomial (v : Nat → R) (m : Monomial) : R := (m.map v).prod
def evaluate (v : Nat → R) (p : Polynomial) : R := (p.map (evaluateMonomial v)).sum

theorem evaluate_insert (v : Nat → R) (x : Nat) (m : Monomial) :
    evaluateMonomial v (insertVariable x m) = v x * evaluateMonomial v m := by
  induction m with
  | nil => simp [insertVariable, evaluateMonomial]
  | cons y ys ih =>
    simp only [insertVariable]
    split
    · simp [evaluateMonomial]
    · change v y * evaluateMonomial v (insertVariable x ys) = v x * (v y * evaluateMonomial v ys)
      rw [ih, mul_left_comm]

theorem evaluate_sort (v : Nat → R) (m : Monomial) :
    evaluateMonomial v (sortMonomial m) = evaluateMonomial v m := by
  induction m with
  | nil => rfl
  | cons x xs ih => rw [sortMonomial, evaluate_insert, ih]; rfl

theorem evaluate_monomial_mul (v : Nat → R) (a b : Monomial) :
    evaluateMonomial v (multiplyMonomial a b) = evaluateMonomial v a * evaluateMonomial v b := by
  rw [multiplyMonomial, evaluate_sort]
  simp [evaluateMonomial]

theorem evaluate_append (v : Nat → R) (a b : Polynomial) :
    evaluate v (a ++ b) = evaluate v a + evaluate v b := by simp [evaluate]

theorem evaluate_multiply (v : Nat → R) (a b : Polynomial) :
    evaluate v (multiply a b) = evaluate v a * evaluate v b := by
  induction a with
  | nil => simp [multiply, evaluate]
  | cons x xs ih =>
    change evaluate v ((b.map (multiplyMonomial x)) ++ multiply xs b) = _
    rw [evaluate_append, ih]
    have hb : evaluate v (b.map (multiplyMonomial x)) = evaluateMonomial v x * evaluate v b := by
      clear ih xs
      induction b with
      | nil => simp [evaluate]
      | cons y ys ih =>
        change evaluateMonomial v (multiplyMonomial x y) + evaluate v (ys.map (multiplyMonomial x)) =
          evaluateMonomial v x * (evaluateMonomial v y + evaluate v ys)
        rw [evaluate_monomial_mul, ih, mul_add]
    rw [hb]
    change _ = (evaluateMonomial v x + evaluate v xs) * evaluate v b
    rw [add_mul]

theorem count_mod_of_coeff (p q : Polynomial) (m : Monomial)
    (h : coefficient p m = coefficient q m) : p.count m % 2 = q.count m % 2 := by
  have hp : (p.filter (· == m)).length = p.count m := by simp [List.count, List.countP_eq_length_filter]
  have hq : (q.filter (· == m)).length = q.count m := by simp [List.count, List.countP_eq_length_filter]
  simp only [coefficient, hp, hq] at h
  have : (p.count m % 2 = 1) ↔ (q.count m % 2 = 1) := by
    simpa only [beq_iff_eq] using Bool.eq_iff_iff.mp h
  omega

variable [CharP R 2]

theorem evaluate_coefficients (v : Nat → R) (p q : Polynomial)
    (h : ∀ m, coefficient p m = coefficient q m) : evaluate v p = evaluate v q := by
  let support := p.toFinset ∪ q.toFinset
  have extend (a : Polynomial) (ha : a.toFinset ⊆ support) :
      evaluate v a = ∑ m ∈ support, (a.count m : R) * evaluateMonomial v m := by
    rw [evaluate, Finset.sum_list_map_count]
    simp only [nsmul_eq_mul]
    have hcount (m : Monomial) : @List.count Monomial (instBEqOfDecidableEq) m a = a.count m := by
      simp only [List.count_eq_countP, Bool.beq_eq_decide_eq]
    simp only [hcount]
    refine Finset.sum_subset (f := fun m => (a.count m : R) * evaluateMonomial v m) ha ?_
    intro m hm hnot
    have : a.count m = 0 := List.count_eq_zero.mpr (by simpa using hnot)
    simp [this]
  rw [extend p (Finset.subset_union_left), extend q (Finset.subset_union_right)]
  apply Finset.sum_congr rfl
  intro m hm
  have hc : (p.count m : R) = (q.count m : R) := by
    calc
      (p.count m : R) = (p.count m % 2 : Nat) := CharTwo.natCast_eq_mod _
      _ = (q.count m % 2 : Nat) := congrArg (fun n : Nat => (n : R)) (count_mod_of_coeff p q m (h m))
      _ = (q.count m : R) := (CharTwo.natCast_eq_mod _).symm
  rw [hc]

omit [CharP R 2] in
theorem evaluate_combination (v : Nat → R) (relations : List Polynomial) (terms : List Term)
    (hr : ∀ r ∈ relations, evaluate v r = 0) : evaluate v (combination relations terms) = 0 := by
  induction terms with
  | nil => simp [combination, evaluate]
  | cons t ts ih =>
    change evaluate v (multiply t.multiplier (relations[t.relation]?.getD []) ++ combination relations ts) = 0
    rw [evaluate_append, evaluate_multiply, ih]
    have hz : evaluate v (relations[t.relation]?.getD []) = 0 := by
      cases he : relations[t.relation]? with
      | none => simp [evaluate]
      | some r => exact hr r (List.mem_of_getElem? he)
    rw [hz, mul_zero, add_zero]

/-- Every valuation into every commutative characteristic-two ring that kills
the imported relations gives the same value to input and output. -/
theorem equalModulo_evaluate (v : Nat → R) (relations : List Polynomial) (input output : Polynomial)
    (h : EqualModuloRelations relations input output)
    (hr : ∀ r ∈ relations, evaluate v r = 0) : evaluate v input = evaluate v output := by
  obtain ⟨terms, _, hc⟩ := h
  have he := evaluate_coefficients v (input ++ output) (combination relations terms) hc
  rw [evaluate_append, evaluate_combination v relations terms hr] at he
  have ht := congrArg (fun z => z + evaluate v output) he
  simpa [add_assoc, CharTwo.add_self_eq_zero] using ht

theorem check_sound_evaluate (v : Nat → R) (relations : List Polynomial) (input output : Polynomial)
    (terms : List Term) (h : check relations input output terms = true)
    (hr : ∀ r ∈ relations, evaluate v r = 0) : evaluate v input = evaluate v output :=
  equalModulo_evaluate v relations input output (check_sound _ _ _ _ h) hr

end NamedElementCertificates
