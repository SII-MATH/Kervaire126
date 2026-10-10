import KIP126.Def.StableHomotopy.TowerSpectralSequence.Filtration.Data
import KIP126.Def.StableHomotopy.TowerSpectralSequence.Pages.Proofs

namespace KIP126.StableHomotopy.TowerSpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

theorem cycleSubmodule_antitone (k n : ℤ) : Antitone (cycleSubmodule T P k n) := by
  intro a b hab
  rcases eq_or_ne b ⊤ with rfl | hb
  · rcases eq_or_ne a ⊤ with rfl | ha
    · exact le_rfl
    · lift a to ℕ using ha
      exact iInf_le _ a
  · lift b to ℕ using hb
    have ha : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) hab
    lift a to ℕ using ha
    exact cycles_antitone T P (a + 1) (b + 1) (by omega) (by omega)
      (Nat.add_le_add_right (WithTop.coe_le_coe.mp hab) 1) k n

theorem boundarySubmodule_monotone (k n : ℤ) : Monotone (boundarySubmodule T P k n) := by
  intro a b hab
  rcases eq_or_ne b ⊤ with rfl | hb
  · rcases eq_or_ne a ⊤ with rfl | ha
    · exact le_rfl
    · lift a to ℕ using ha
      change boundaries T P (a + 1) (by omega) k n ≤
        ⨆ m : ℕ, boundaries T P (m + 1) (by omega) k n
      exact le_iSup (fun m : ℕ => boundaries T P (m + 1) (by omega) k n) a
  · lift b to ℕ using hb
    have ha : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) hab
    lift a to ℕ using ha
    exact boundaries_monotone T P (a + 1) (b + 1) (by omega) (by omega)
      (Nat.add_le_add_right (WithTop.coe_le_coe.mp hab) 1) k n

theorem cycleSubmodule_zero (k n : ℤ) : cycleSubmodule T P k n 0 = ⊤ :=
  cycles_one T P k n

theorem boundarySubmodule_le_cycle (k n : ℤ) (r : WithTop ℕ) :
    boundarySubmodule T P k n r ≤ cycleSubmodule T P k n r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · exact iSup_le fun a => le_iInf fun b =>
      boundaries_le_cycles T P (a + 1) (b + 1) (by omega) (by omega) k n
  · lift r to ℕ using hr
    exact boundaries_le_cycles T P (r + 1) (r + 1) (by omega) (by omega) k n

end KIP126.StableHomotopy.TowerSpectralSequence
