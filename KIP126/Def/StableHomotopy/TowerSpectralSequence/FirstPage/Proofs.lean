import KIP126.Def.StableHomotopy.TowerSpectralSequence.FirstPage.Data

/-! Representative compatibility for the prescribed first-page maps. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- The ordinary quotient equivalence sends the class of a cycle to its
actual underlying E₁ representative. -/
@[simp] theorem rawFirstPageEquiv_mk (k n : ℤ)
    (x : cycles T P 1 (by omega) k n) :
    rawFirstPageEquiv T P k n ((cycleBoundaries T P 1 (by omega) k n).mkQ x) =
      x.val := rfl

/-- The representative projection is the specified quotient construction. -/
theorem firstPageProjection_apply (k n : ℤ) (x : E1 T P k n) :
    (firstPageProjection T P k n).hom x =
      (pageIso T P k n 0).inv.hom
        ((cycleBoundaries T P 1 (by omega) k n).mkQ
          ((cyclesOneEquiv T P k n).symm x)) := rfl

/-- The actual representative projection is the inverse of the fixed
first-page identification, not an independent map. -/
theorem firstPageProjection_eq_inv (k n : ℤ) :
    firstPageProjection T P k n = (firstPageIso T P k n).inv := by
  rfl

/-- Taking the E₁ value of the actual projected representative returns
precisely that representative. -/
@[simp] theorem firstPageIso_projection (k n : ℤ) (x : E1 T P k n) :
    (firstPageIso T P k n).hom.hom ((firstPageProjection T P k n).hom x) = x := by
  rw [firstPageProjection_eq_inv]
  change ((firstPageIso T P k n).inv ≫ (firstPageIso T P k n).hom).hom x = x
  rw [Iso.inv_hom_id]
  rfl

end KIP126.StableHomotopy.TowerSpectralSequence
