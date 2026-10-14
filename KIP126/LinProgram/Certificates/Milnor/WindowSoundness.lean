module

public import KIP126.LinProgram.Certificates.Milnor.Grading
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section


namespace MilnorCertificates
open scoped BigOperators

theorem exponent_le_weight (m : Monomial) (j : Nat) (hj : j < m.length) :
    m[j] ≤ weight m := by
  rw [weight_eq_coordinateWeight]
  unfold coordinateWeight
  have hc : 1 ≤ 2^(j+1)-1 := by
    have hp : 0 < 2^j := Nat.two_pow_pos _
    rw [Nat.pow_succ]
    omega
  have hm : m[j] ≤ m[j]*(2^(j+1)-1) := by
    have hh := Nat.mul_le_mul_left m[j] hc
    simpa using hh
  apply hm.trans
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range m.length) =>
    Nat.zero_le ((m[i]?.getD 0)*(2^(i+1)-1))) (Finset.mem_range.mpr hj)
  simpa [hj] using hh

theorem exponentVectors_complete (m : Monomial) (bound : Nat)
    (h : ∀ x ∈ m, x ≤ bound) : m ∈ exponentVectors m.length bound := by
  induction m with
  | nil => simp [exponentVectors]
  | cons a xs ih =>
    simp only [List.length_cons, exponentVectors, List.mem_flatMap, List.mem_map]
    exact ⟨a, List.mem_range.mpr (by have := h a (by simp); omega), xs,
      ih (fun x hx => h x (by simp [hx])), rfl⟩

theorem basis_complete (rank bound : Nat) (m : Monomial)
    (hm : m.length = rank) (hw : weight m ≤ bound) : m ∈ basis rank bound := by
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa using hw⟩
  rw [← hm]
  apply exponentVectors_complete
  intro x hx
  obtain ⟨j,hj,hx⟩ := List.mem_iff_getElem.mp hx
  subst x
  exact (exponent_le_weight m j hj).trans hw

theorem coefficient_outside_window (w : Window) (p : Polynomial)
    (hp : polynomialInWindow w.rank w.degree p = true) (m : Monomial)
    (hw : w.degree < weight m) : coefficient p m = false := by
  cases he : coefficient p m
  · rfl
  · have hm := coefficient_true_mem p m he
    have hh := List.all_eq_true.mp hp m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
    omega

/-- Finite checking yields equality at every monomial of the declared rank.
Input homogeneity and the degree bound discharge all omitted higher degrees. -/
theorem isMilnorProduct_all_monomials (w : Window) (left right output : Polynomial)
    (d e : Nat) (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (hbound : d+e ≤ w.degree) (h : IsMilnorProduct w left right output)
    (m : Monomial) (hm : m.length = w.rank) :
    coefficient output m = pairTensor left right (coproduct w.rank m) := by
  by_cases hw : weight m ≤ w.degree
  · exact h.2.2.2 m (basis_complete w.rank w.degree m hm hw)
  · have hout := coefficient_outside_window w output h.2.2.1 m (by omega)
    have hprod := product_degree_support w.rank d e left right hl hr m hm (by omega)
    rw [hout,hprod]

theorem check_all_monomials (w : Window) (left right output : Polynomial) (c : Certificate)
    (d e : Nat) (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (hbound : d+e ≤ w.degree) (h : check w left right output c = true) :
    ∀ m, m.length = w.rank →
      coefficient output m = pairTensor left right (coproduct w.rank m) :=
  isMilnorProduct_all_monomials w left right output d e hl hr hbound (check_sound _ _ _ _ _ h)

#print axioms basis_complete
#print axioms check_all_monomials

end MilnorCertificates
