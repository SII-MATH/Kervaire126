import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Lifting.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  {H : Mod2EilenbergMacLane (C := C)} (B : SphereH6BoundaryLifts H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Three actual connecting-map lift equations: through ΣT₄ → ΣT₃ for
the square and through ΣT₆ → ΣT₅ for the cross terms. These conditions
can be stated without a long-layer product or an E₂-page product. -/
structure SphereH6BoundaryLifts.FitsProducts : Prop where
  square : B.square ≫ (adamsTowerMapAt H.unit (𝟙_ C) 3 4 (by decide))⟦(1 : ℤ)⟧' =
    adamsSphereLongLayerProductBoundary H R 2 (by decide) 1 1
  left : B.left ≫ (adamsTowerMapAt H.unit (𝟙_ C) 5 6 (by decide))⟦(1 : ℤ)⟧' =
    adamsSphereLongLayerProductBoundary H R 2 (by decide) 3 1
  right : B.right ≫ (adamsTowerMapAt H.unit (𝟙_ C) 5 6 (by decide))⟦(1 : ℤ)⟧' =
    adamsSphereLongLayerProductBoundary H R 2 (by decide) 1 3

end
end KIP126.Classical.Adams
