import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.One.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Page.Proofs
import KIP126.Def.StableHomotopy.Context.TensorPairing.Proofs

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

theorem longLayerOneComposition_projection (X Y Z : C) (s t : ℕ) :
    longLayerOneComposition H R X Y Z s t ≫
      adamsLongLayerProjection H.unit (mappingObject X Z) 1 le_rfl
        ((s : ℤ) + (t : ℤ)) = longLayerProjectedComposition H R X Y Z 1 le_rfl s t := by
  simp [longLayerOneComposition]

/-- The required mixed representative compatibility is proved from the actual
spectrum-level square; it is not a new hypothesis. -/
theorem longLayerOnePairing_projection [MonoidalPreadditive C]
    (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    (longLayerOnePairing H R X Y Z s t u v).ProjectionCompatible := by
  intro a b
  exact homotopyTensorPairing_naturality _ _ _ (by omega)
    (longLayerOneComposition H R X Y Z s t) (layerCompositionOrdered H R X Y Z s t)
    _ _ _ (longLayerOneComposition_projection H R X Y Z s t) a b

/-- This actual first quotient-page pairing exists and is determined by the
concrete long-layer representatives. This is the tower's page one, not the
internal sequence's out-of-range Page 1, and asserts no higher Leibniz law. -/
theorem firstQuotientPairing_exists [MonoidalPreadditive C]
    (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    ∃ F : adamsPage H.unit (mappingObject X Y) 1 le_rfl s u →ₗ[ℤ]
      adamsPage H.unit (mappingObject Y Z) 1 le_rfl t v →ₗ[ℤ]
        adamsPage H.unit (mappingObject X Z) 1 le_rfl ((s : ℤ) + (t : ℤ)) (u + v),
      ∀ a b, F (adamsLongLayerToPage H.unit (mappingObject X Y) 1 le_rfl s u a)
        (adamsLongLayerToPage H.unit (mappingObject Y Z) 1 le_rfl t v b) =
          adamsLongLayerToPage H.unit (mappingObject X Z) 1 le_rfl
            ((s : ℤ) + (t : ℤ)) (u + v) ((longLayerOnePairing H R X Y Z s t u v).long a b) := by
  let P := longLayerOnePairing H R X Y Z s t u v
  have hP := longLayerOnePairing_projection H R X Y Z s t u v
  have hB := MixedAdamsLongLayerPairing.boundaryCompatible_one P
  exact ⟨P.onPage hP hB, P.onPage_long hP hB⟩

end
end KIP126.Classical.Adams.Moss
