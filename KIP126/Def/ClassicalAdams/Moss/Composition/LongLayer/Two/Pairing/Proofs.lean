import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Two.Pairing.Data
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Proofs
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
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

theorem longLayerTwoComposition_projection (X Y Z : C) (s t : ℕ) :
    longLayerTwoComposition H R X Y Z s t ≫
      adamsLongLayerProjection H.unit (mappingObject X Z) 2 (by decide)
        ((s : ℤ) + (t : ℤ)) = longLayerProjectedComposition H R X Y Z 2 (by decide) s t :=
  (longLayerTwoComposition_exists H R X Y Z s t).choose_spec

/-- The representative operations commute with the actual long-layer
projections. This is proved from the spectrum-level lift, not assumed. -/
theorem longLayerTwoPairing_projection [MonoidalPreadditive C]
    (X Y Z : C) (s t : ℕ) (u v : ℤ) :
    (longLayerTwoPairing H R X Y Z s t u v).ProjectionCompatible := by
  intro a b
  exact homotopyTensorPairing_naturality _ _ _ (by omega)
    (longLayerTwoComposition H R X Y Z s t) (layerCompositionOrdered H R X Y Z s t)
    _ _ _ (longLayerTwoComposition_projection H R X Y Z s t) a b

/-- The prescribed first-layer composition preserves actual second-page
cycles. Descent to their boundary quotient remains a separate obligation. -/
theorem firstComposition_mem_cycles_two [MonoidalPreadditive C]
    (X Y Z : C) (s t : ℕ) (u v : ℤ)
    (x : adamsE1 H.unit (mappingObject X Y) s u)
    (hx : x ∈ adamsCycles H.unit (mappingObject X Y) 2 (by decide) s u)
    (y : adamsE1 H.unit (mappingObject Y Z) t v)
    (hy : y ∈ adamsCycles H.unit (mappingObject Y Z) 2 (by decide) t v) :
    firstComposition H R X Y Z s t u v x y ∈
      adamsCycles H.unit (mappingObject X Z) 2 (by decide) ((s : ℤ) + (t : ℤ)) (u + v) :=
  (longLayerTwoPairing H R X Y Z s t u v).mem_cycles
    (longLayerTwoPairing_projection H R X Y Z s t u v) x hx y hy

end
end KIP126.Classical.Adams.Moss
