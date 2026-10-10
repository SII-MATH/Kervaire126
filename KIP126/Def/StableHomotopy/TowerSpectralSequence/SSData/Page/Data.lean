import KIP126.Def.StableHomotopy.TowerSpectralSequence.SSData.Data
import KIP126.Def.SpectralSequence.ModuleQuotient.Data

/-! Canonical identification with the quotient of the very same cycle and
boundary submodules. No additional comparison is chosen. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

noncomputable def pageIso (k n : ℤ) (m : ℕ) :
    (ssData T P k n).page (m : WithTop ℕ) ≅
      ModuleCat.of ℤ (page T P (m + 1) (by omega) k n) :=
  submoduleCokernelIso (M := ModuleCat.of ℤ (E1 T P k n))
    (boundaries T P (m + 1) (by omega) k n)
    (cycles T P (m + 1) (by omega) k n)
    (boundaries_le_cycles T P (m + 1) (m + 1) (by omega) (by omega) k n)

end KIP126.StableHomotopy.TowerSpectralSequence
