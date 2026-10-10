import KIP126.Def.StableHomotopy.TowerSpectralSequence.SSData.Page.Data

/-!
The actual first quotient page equals the original layer Hom group: its
cycle submodule is top and its boundary submodule is bottom. The maps below
are the subtype, quotient and categorical-quotient maps of these very
submodules, with no separately selected first-page comparison.
-/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- All first-page elements are cycles; the forward map forgets only the
redundant membership proof. -/
noncomputable def cyclesOneEquiv (k n : ℤ) :
    cycles T P 1 (by omega) k n ≃ₗ[ℤ] E1 T P k n where
  toFun := Subtype.val
  invFun x := ⟨x, by rw [cycles_one]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Quotienting first-page cycles by their actual zero boundary submodule
recovers the original E₁ group. -/
noncomputable def rawFirstPageEquiv (k n : ℤ) :
    page T P 1 (by omega) k n ≃ₗ[ℤ] E1 T P k n :=
  ((cycleBoundaries T P 1 (by omega) k n).quotEquivOfEqBot (by
    rw [cycleBoundaries, boundaries_one, Submodule.comap_bot, Submodule.ker_subtype])).trans
      (cyclesOneEquiv T P k n)

/-- The actual stage-zero categorical page, identified through the same
submodule quotient with the original layer Hom group. -/
noncomputable def firstPageIso (k n : ℤ) :
    (ssData T P k n).page 0 ≅ ModuleCat.of ℤ (E1 T P k n) :=
  pageIso T P k n 0 ≪≫ (rawFirstPageEquiv T P k n).toModuleIso

/-- Send an actual E₁ representative through the cycle inclusion and quotient
map, then through the fixed categorical-quotient comparison. -/
noncomputable def firstPageProjection (k n : ℤ) :
    ModuleCat.of ℤ (E1 T P k n) ⟶ (ssData T P k n).page 0 :=
  ModuleCat.ofHom
    ((cycleBoundaries T P 1 (by omega) k n).mkQ.comp
      (cyclesOneEquiv T P k n).symm.toLinearMap) ≫
    (pageIso T P k n 0).inv

end KIP126.StableHomotopy.TowerSpectralSequence
