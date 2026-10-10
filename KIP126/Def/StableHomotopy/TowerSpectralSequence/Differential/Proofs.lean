import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Data

/-! Representative formula and square-zero for the actual quotient map. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- On every actual cycle representative the descended differential is
the previously specified J(lift(K(x))) quotient value. -/
@[simp] theorem differential_mk (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) :
    differential T P q hq k n ((cycleBoundaries T P q hq k n).mkQ x) =
      differentialValue T P q hq k n x := rfl

/-- An actual tower-to-layer class has zero connecting image and differential. -/
theorem differential_JToPage (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : ShiftedHom P n (T.obj k)) :
    differential T P q hq k n (JToPage T P q hq k n x) = 0 := by
  change differentialValue T P q hq k n (JToCycles T P q hq k n x) = 0
  apply differentialValue_eq_zero_of_K
  exact (RepresentedHom.exact_g P (T.layerCofiberSequence k) n _).2 ⟨x, rfl⟩

/-- The constructed intrinsic page differential squares to zero. -/
theorem differential_comp (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : page T P q hq k n) :
    differential T P q hq (k + q) (n - 1) (differential T P q hq k n x) = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change differential T P q hq (k + q) (n - 1)
      (JToPage T P q hq (k + q) (n - 1) (cycleLift T P q hq k n x)) = 0
    exact differential_JToPage T P q hq (k + q) (n - 1) _

end KIP126.StableHomotopy.TowerSpectralSequence
