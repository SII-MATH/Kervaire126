import KIP126.Def.ClassicalAdams.TowerLongLayer.Data
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Homotopy.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The prescribed product of the two long-layer projections, still valued
in the original one-step layer. This map exists before any long-layer product. -/
def adamsSphereLongLayerProjectedProduct (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    adamsLongLayer H.unit (𝟙_ C) r hr s ⊗ adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
      adamsLayerAt H.unit (𝟙_ C) ((s : ℤ) + (t : ℤ)) :=
  (adamsLongLayerProjection H.unit (𝟙_ C) r hr s ⊗ₘ
    adamsLongLayerProjection H.unit (𝟙_ C) r hr t) ≫
      adamsSphereLayerProductOrdered H R s t

/-- The actual connecting map of that prescribed product. Lifting this
through the suspended tower composite is the precise existence obstruction
for a projection-compatible long-layer spectrum product. -/
def adamsSphereLongLayerProductBoundary (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    adamsLongLayer H.unit (𝟙_ C) r hr s ⊗ adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
      (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + 1))⟦(1 : ℤ)⟧ :=
  adamsSphereLongLayerProjectedProduct H R r hr s t ≫
    HasFunctorialCofiber.cofibδ
      (adamsTowerMapAt H.unit (𝟙_ C) ((s : ℤ) + (t : ℤ))
        (((s : ℤ) + (t : ℤ)) + 1) (by omega))

end
end KIP126.Classical.Adams
