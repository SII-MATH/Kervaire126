import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Lifting.Proofs

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- An exact criterion using the constructed first-layer composition, not a
freely supplied long-layer pairing. For r=2 the missing map lifts its boundary
through ΣT_(s+t+2) → ΣT_(s+t+1). This theorem does not assert such a lift. -/
theorem longLayerComposition_exists_iff_boundaryLift
    (X Y Z : C) (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    (∃ μ : adamsLongLayer H.unit (mappingObject X Y) r hr s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) r hr t ⟶
        adamsLongLayer H.unit (mappingObject X Z) r hr ((s : ℤ) + (t : ℤ)),
      μ ≫ adamsLongLayerProjection H.unit (mappingObject X Z) r hr
        ((s : ℤ) + (t : ℤ)) = longLayerProjectedComposition H R X Y Z r hr s t) ↔
      ∃ y : adamsLongLayer H.unit (mappingObject X Y) r hr s ⊗
        adamsLongLayer H.unit (mappingObject Y Z) r hr t ⟶
          (adamsTowerAt H.unit (mappingObject X Z) (((s : ℤ) + (t : ℤ)) + r))⟦(1 : ℤ)⟧,
        y ≫ (adamsTowerMapAt H.unit (mappingObject X Z) (((s : ℤ) + (t : ℤ)) + 1)
          (((s : ℤ) + (t : ℤ)) + r) (by omega))⟦(1 : ℤ)⟧' =
            longLayerCompositionBoundary H R X Y Z r hr s t :=
  adamsLongLayerProjection_lift_iff H.unit (mappingObject X Z) r hr
    ((s : ℤ) + (t : ℤ)) (longLayerProjectedComposition H R X Y Z r hr s t)

end
end KIP126.Classical.Adams.Moss
