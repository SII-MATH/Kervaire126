import KIP126.Def.StableHomotopy.TowerSpectralSequence.Pages.Proofs

/-! The intrinsic differential value is J(lift(K(x))) in the target
quotient. Its formula uses only the actual tower and a witnessed lift. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

noncomputable def JToCycles (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    ShiftedHom P n (T.obj k) →ₗ[ℤ] cycles T P q hq k n :=
  (J T P k n).codRestrict _ (J_mem_cycles T P q hq k n)

noncomputable def JToPage (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    ShiftedHom P n (T.obj k) →ₗ[ℤ] page T P q hq k n :=
  (cycleBoundaries T P q hq k n).mkQ.comp (JToCycles T P q hq k n)

noncomputable def differentialValue (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) : page T P q hq (k + q) (n - 1) :=
  JToPage T P q hq (k + q) (n - 1) (cycleLift T P q hq k n x)

end KIP126.StableHomotopy.TowerSpectralSequence
