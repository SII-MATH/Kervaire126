import KIP126.Def.StableHomotopy.TowerSpectralSequence.Filtration.Proofs
import KIP126.Def.SpectralSequence.Basic.Data
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-! The tower's actual E₁-based nested-subobject data. It is defined before
the differential and neither consumes a spectral sequence nor selects one. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

noncomputable def ssData (k n : ℤ) : SSData (ModuleCat.{v} ℤ) where
  V := ModuleCat.of ℤ (E1 T P k n)
  Z r := (ModuleCat.subobjectModule _).symm (cycleSubmodule T P k n r)
  B r := (ModuleCat.subobjectModule _).symm (boundarySubmodule T P k n r)
  Z_anti := (ModuleCat.subobjectModule _).symm.monotone.comp_antitone
    (cycleSubmodule_antitone T P k n)
  B_mono := (ModuleCat.subobjectModule _).symm.monotone.comp
    (boundarySubmodule_monotone T P k n)
  Z_zero := by
    change (ModuleCat.subobjectModule (ModuleCat.of ℤ (E1 T P k n))).symm
      (cycleSubmodule T P k n 0) = ⊤
    rw [cycleSubmodule_zero, OrderIso.map_top]
  B_le_Z r := (ModuleCat.subobjectModule _).symm.monotone
    (boundarySubmodule_le_cycle T P k n r)
  Z_top_greatest A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) A ≤
      (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm _)
    rw [OrderIso.apply_symm_apply]
    change (ModuleCat.subobjectModule _) A ≤ ⨅ m : ℕ, cycles T P (m + 1) (by omega) k n
    refine le_iInf fun m => ?_
    have hm := (ModuleCat.subobjectModule _).monotone (h m)
    rw [OrderIso.apply_symm_apply] at hm
    exact hm
  B_top_least A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm _) ≤
      (ModuleCat.subobjectModule _) A
    rw [OrderIso.apply_symm_apply]
    change (⨆ m : ℕ, boundaries T P (m + 1) (by omega) k n) ≤ (ModuleCat.subobjectModule _) A
    refine iSup_le fun m => ?_
    have hm := (ModuleCat.subobjectModule _).monotone (h m)
    rw [OrderIso.apply_symm_apply] at hm
    exact hm

end KIP126.StableHomotopy.TowerSpectralSequence
