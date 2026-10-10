import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Lifting.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Lifting.Proofs

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

/-- Construct a product matching both its projection and the specified
lifted connecting morphism. The latter is needed for differential formulas. -/
theorem adamsSphereLongLayerProduct_exists_of_boundaryLift
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ)
    (y : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
      adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
        (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))⟦(1 : ℤ)⟧)
    (hy : y ≫ (adamsTowerMapAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + 1)
      (((s : ℤ) + (t : ℤ)) + r) (by omega))⟦(1 : ℤ)⟧' =
        adamsSphereLongLayerProductBoundary H R r hr s t) :
    ∃ μ : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
      adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
        adamsLongLayer H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)),
      μ ≫ adamsLongLayerProjection H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) =
        adamsSphereLongLayerProjectedProduct H R r hr s t ∧
      μ ≫ HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit (𝟙_ C) ((s : ℤ) + (t : ℤ))
          (((s : ℤ) + (t : ℤ)) + r) (by omega)) = y :=
  adamsLongLayerProjection_lift_of_boundary H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ))
    (adamsSphereLongLayerProjectedProduct H R r hr s t) y hy

/-- Exact spectrum-level existence criterion. In particular, no product of
long layers or its projection square is an input on the right-hand side. -/
theorem adamsSphereLongLayerProduct_exists_iff_boundaryLift
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    (∃ μ : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
      adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
        adamsLongLayer H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)),
      μ ≫ adamsLongLayerProjection H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) =
        adamsSphereLongLayerProjectedProduct H R r hr s t) ↔
      ∃ y : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
        adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
          (adamsTowerAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + r))⟦(1 : ℤ)⟧,
        y ≫ (adamsTowerMapAt H.unit (𝟙_ C) (((s : ℤ) + (t : ℤ)) + 1)
          (((s : ℤ) + (t : ℤ)) + r) (by omega))⟦(1 : ℤ)⟧' =
            adamsSphereLongLayerProductBoundary H R r hr s t :=
  adamsLongLayerProjection_lift_iff H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ))
    (adamsSphereLongLayerProjectedProduct H R r hr s t)

end
end KIP126.Classical.Adams
