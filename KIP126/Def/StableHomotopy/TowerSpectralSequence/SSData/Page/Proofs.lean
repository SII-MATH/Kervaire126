import KIP126.Def.StableHomotopy.TowerSpectralSequence.SSData.Page.Data
import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs

namespace KIP126.StableHomotopy.TowerSpectralSequence
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- The existing page comparison preserves the actual cycle representative. -/
@[reassoc] theorem pageIso_π (k n : ℤ) (m : ℕ) :
    (submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P k n))
      (cycles T P (m + 1) (by omega) k n)).inv ≫
      (ssData T P k n).pageπ (m : WithTop ℕ) ≫ (pageIso T P k n m).hom =
    ModuleCat.ofHom (cycleBoundaries T P (m + 1) (by omega) k n).mkQ :=
  submoduleCokernelIso_π _ _ _

/-- Every categorical page class has a representative in the existing cycle module. -/
theorem projection_surjective (k n : ℤ) (m : ℕ) :
    Function.Surjective (fun x : cycles T P (m + 1) (by omega) k n =>
      (ssData T P k n).pageπ (m : WithTop ℕ)
        ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P k n))
          (cycles T P (m + 1) (by omega) k n)).inv x)) := by
  apply Function.Surjective.comp
  · exact (ModuleCat.epi_iff_surjective _).mp
      (inferInstanceAs (Epi (cokernel.π _)))
  · exact (ModuleCat.epi_iff_surjective _).mp inferInstance
end KIP126.StableHomotopy.TowerSpectralSequence
