import KIP126.Def.StableHomotopy.TowerSpectralSequence.Pages.Data
import Mathlib.Order.WithBot

/-! The intrinsic E₁-based nested cycles and boundaries. Internal stage m
is raw page m+1; the infinite stages are their actual infimum and supremum. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

noncomputable def cycleSubmodule (k n : ℤ) : WithTop ℕ → Submodule ℤ (E1 T P k n)
  | ⊤ => ⨅ m : ℕ, cycles T P (m + 1) (by omega) k n
  | (m : ℕ) => cycles T P (m + 1) (by omega) k n

noncomputable def boundarySubmodule (k n : ℤ) : WithTop ℕ → Submodule ℤ (E1 T P k n)
  | ⊤ => ⨆ m : ℕ, boundaries T P (m + 1) (by omega) k n
  | (m : ℕ) => boundaries T P (m + 1) (by omega) k n

end KIP126.StableHomotopy.TowerSpectralSequence
