import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} (M : SphereH6LongLayerMaps H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Spectrum projection squares and the two-sided tower-kernel boundary
conditions for just the three required products. These are proof obligations
on actual maps, not a project axiom or a supplied E₂ multiplication. -/
structure SphereH6LongLayerMaps.Compatible : Prop where
  square_projection : M.square ≫ adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 2 =
    (adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 1 ⊗ₘ
      adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 1) ≫
        adamsSphereLayerProductOrdered H R 1 1
  left_projection : M.left ≫ adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 4 =
    (adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 3 ⊗ₘ
      adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 1) ≫
        adamsSphereLayerProductOrdered H R 3 1
  right_projection : M.right ≫ adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 4 =
    (adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 1 ⊗ₘ
      adamsLongLayerProjection H.unit (𝟙_ C) 2 (by decide) 3) ≫
        adamsSphereLayerProductOrdered H R 1 3
  square_boundary : (M.squarePairing R).BoundaryCompatible
  left_boundary : (M.leftPairing R).BoundaryCompatible
  right_boundary : (M.rightPairing R).BoundaryCompatible

end
end KIP126.Classical.Adams
