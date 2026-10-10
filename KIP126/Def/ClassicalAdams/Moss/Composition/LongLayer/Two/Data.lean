import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Data

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- The obstruction to lifting the fixed length-two projected composition:
its actual connecting map followed by the next tower-to-layer map. Both
arrows are prescribed; this is not an independently supplied obstruction. -/
def longLayerTwoCompositionObstruction (X Y Z : C) (s t : ℕ) :
    adamsLongLayer H.unit (mappingObject X Y) 2 (by decide) s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) 2 (by decide) t ⟶
        (adamsLayerAt H.unit (mappingObject X Z)
          (((s : ℤ) + (t : ℤ)) + 1))⟦(1 : ℤ)⟧ :=
  longLayerCompositionBoundary H R X Y Z 2 (by decide) s t ≫
    (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Z)
      (((s : ℤ) + (t : ℤ)) + 1) ((((s : ℤ) + (t : ℤ)) + 1) + 1) (by omega)))⟦(1 : ℤ)⟧'

end
end KIP126.Classical.Adams.Moss
