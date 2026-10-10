import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Predicates
import KIP126.Def.StableHomotopy.Context.TensorPairing.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The spectrum-level projection square supplies the previously separate
representative compatibility. The first-page product is the fixed one. -/
theorem adamsSphereLongLayerPairing_projection (r : ℕ) (hr : 1 ≤ r)
    (s t : ℕ) (u v : ℤ)
    (μ : adamsLongLayer H.unit (𝟙_ C) r hr s ⊗
      adamsLongLayer H.unit (𝟙_ C) r hr t ⟶
        adamsLongLayer H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)))
    (hμ : μ ≫ adamsLongLayerProjection H.unit (𝟙_ C) r hr ((s : ℤ) + (t : ℤ)) =
      (adamsLongLayerProjection H.unit (𝟙_ C) r hr s ⊗ₘ
        adamsLongLayerProjection H.unit (𝟙_ C) r hr t) ≫
          adamsSphereLayerProductOrdered H R s t) :
    (adamsSphereLongLayerPairing H R r hr s t u v μ).ProjectionCompatible := by
  intro a b
  exact homotopyTensorPairing_naturality _ _ _ (by omega) μ
    (adamsSphereLayerProductOrdered H R s t) _ _ _ hμ a b

end
end KIP126.Classical.Adams
