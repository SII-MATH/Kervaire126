import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Two.Proofs
import KIP126.Def.ClassicalAdams.Moss.Composition.CoefficientCycles.Layer.Proofs

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))

private theorem firstBoundary_zero_transport {U : C} (A : C)
    (i j : ℤ) (h : i = j) (a : U ⟶ adamsLayerAt H.unit A i)
    (ha : a ≫ HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit A i (i + 1) (by omega)) ≫
      (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit A (i + 1) ((i + 1) + 1) (by omega)))⟦(1 : ℤ)⟧' = 0) :
    a ≫ eqToHom (congrArg (adamsLayerAt H.unit A) h) ≫
      HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit A j (j + 1) (by omega)) ≫
      (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt H.unit A (j + 1) ((j + 1) + 1) (by omega)))⟦(1 : ℤ)⟧' = 0 := by
  subst j
  simpa only [eqToHom_refl, Category.id_comp] using ha

variable [MonoidalClosed C] [BraidedCategory C]
  (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The length-two composition obstruction vanishes on the entire tensor
of long layers. Each input projection is a first-boundary cycle and the
actual ring coefficient multiplication preserves the corresponding unit
equalizer. No long-layer lift or pagewise Leibniz rule is assumed. -/
theorem longLayerTwoCompositionObstruction_eq_zero
    (X Y Z : C) (s t : ℕ) :
    longLayerTwoCompositionObstruction H R X Y Z s t = 0 := by
  have hz := layerComposition_firstBoundary_eq_zero H R X Y Z s t
    (adamsLongLayerProjection H.unit (mappingObject X Y) 2 (by decide) s)
    (adamsLongLayerProjection H.unit (mappingObject Y Z) 2 (by decide) t)
    (longLayerTwoProjection_firstBoundary_eq_zero H (mappingObject X Y) s)
    (longLayerTwoProjection_firstBoundary_eq_zero H (mappingObject Y Z) t)
  have ht := firstBoundary_zero_transport H (mappingObject X Z)
    ((t + s : ℕ) : ℤ) ((s : ℤ) + (t : ℤ)) (by omega) _ hz
  simpa only [longLayerTwoCompositionObstruction, longLayerCompositionBoundary,
    longLayerProjectedComposition, layerCompositionOrdered, Category.assoc] using ht

/-- The specified projected composition has an actual length-two lift.
Existence is proved from the ring structure and distinguished triangles. -/
theorem longLayerTwoComposition_exists (X Y Z : C) (s t : ℕ) :
    ∃ μ : adamsLongLayer H.unit (mappingObject X Y) 2 (by decide) s ⊗
        adamsLongLayer H.unit (mappingObject Y Z) 2 (by decide) t ⟶
      adamsLongLayer H.unit (mappingObject X Z) 2 (by decide) ((s : ℤ) + (t : ℤ)),
      μ ≫ adamsLongLayerProjection H.unit (mappingObject X Z) 2 (by decide)
        ((s : ℤ) + (t : ℤ)) = longLayerProjectedComposition H R X Y Z 2 (by decide) s t :=
  (longLayerTwoComposition_exists_iff_obstruction_eq_zero H R X Y Z s t).mpr
    (longLayerTwoCompositionObstruction_eq_zero H R X Y Z s t)

end
end KIP126.Classical.Adams.Moss
