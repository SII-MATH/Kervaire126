import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Cycles.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)
  (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible)

include hB

theorem AdamsLongLayerPairing.boundaries_le_left_ker :
    adamsCycleBoundaries unit X r hr p.1 p.2 ≤ (P.cyclesToPage hP).ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  change (adamsCycleBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)).mkQ
    (P.onCycles hP x y) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact P.boundary_left hB x.val hx y.val y.property

theorem AdamsLongLayerPairing.boundaries_le_right_ker :
    adamsCycleBoundaries unit X r hr q.1 q.2 ≤ (P.cyclesToPage hP).flip.ker := by
  intro y hy
  apply LinearMap.ext
  intro x
  change (adamsCycleBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)).mkQ
    (P.onCycles hP x y) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact P.boundary_right hB x.val x.property y.val hy

end
end KIP126.Classical.Adams
