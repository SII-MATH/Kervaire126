import KIP126.Def.ClassicalAdams.TowerLongLayer.Boundary.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

theorem adamsDifferential_longLayerToPage_eq_boundary (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (z : HomotopyGroup (t - s) (adamsLongLayer unit X r hr s)) :
    adamsDifferential unit X r hr s t (adamsLongLayerToPage unit X r hr s t z) =
      adamsLongLayerBoundaryToPage unit X r hr s t z :=
  adamsDifferential_longLayerToPage unit X r hr s t z

end
end KIP126.Classical.Adams
