import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Value.Data

/-!
Independence of the witnessed lift and linearity of the actual J(lift(K(x)))
value. All equalities are in the specified target quotient, so no linear
choice of lifts is assumed.
-/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- Tower classes with the same image q-1 steps below have the same layer
class modulo the actual q-boundaries. -/
theorem JToPage_eq (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x y : ShiftedHom P n (T.obj k))
    (h : I T P n (k - q + 1) k (by omega) x =
      I T P n (k - q + 1) k (by omega) y) :
    JToPage T P q hq k n x = JToPage T P q hq k n y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).2
  change J T P k n (x - y) ∈ boundaries T P q hq k n
  refine ⟨x - y, ?_, rfl⟩
  change I T P n (k - q + 1) k _ (x - y) = 0
  rw [map_sub, h, sub_self]

/-- Every actual lift of the same connecting image computes the specified
differential value in the target quotient. -/
theorem differentialValue_eq_of_lift (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n)
    (y : ShiftedHom P (n - 1) (T.obj (k + q)))
    (hy : I T P (n - 1) (k + 1) (k + q) (by omega) y = K T P k n x) :
    differentialValue T P q hq k n x = JToPage T P q hq (k + q) (n - 1) y := by
  unfold differentialValue
  apply JToPage_eq
  have H (j : ℤ) (hj : j ≤ k + q) (he : j = k + 1) :
      I T P (n - 1) j (k + q) hj (cycleLift T P q hq k n x) =
        I T P (n - 1) j (k + q) hj y := by
    subst j
    exact (cycleLift_spec T P q hq k n x).trans hy.symm
  exact H _ _ (by omega)

/-- A zero connecting image gives a zero differential in the target quotient. -/
theorem differentialValue_eq_zero_of_K (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) (hx : K T P k n x = 0) :
    differentialValue T P q hq k n x = 0 := by
  rw [differentialValue_eq_of_lift T P q hq k n x 0 (by rw [map_zero, hx]), map_zero]

/-- The quotient value is additive even though the chosen lift need not be. -/
theorem differentialValue_add (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x y : cycles T P q hq k n) :
    differentialValue T P q hq k n (x + y) =
      differentialValue T P q hq k n x + differentialValue T P q hq k n y := by
  rw [differentialValue_eq_of_lift T P q hq k n (x + y)
    (cycleLift T P q hq k n x + cycleLift T P q hq k n y) (by
      rw [map_add, cycleLift_spec, cycleLift_spec]
      exact (map_add (K T P k n) _ _).symm)]
  exact map_add _ _ _

/-- The quotient value respects the canonical integer scalar action. -/
theorem differentialValue_smul (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (a : ℤ) (x : cycles T P q hq k n) :
    differentialValue T P q hq k n (a • x) =
      a • differentialValue T P q hq k n x := by
  rw [differentialValue_eq_of_lift T P q hq k n (a • x)
    (a • cycleLift T P q hq k n x) (by
      rw [map_smul, cycleLift_spec]
      exact (map_smul (K T P k n) a x.val).symm)]
  exact map_smul _ _ _

end KIP126.StableHomotopy.TowerSpectralSequence
