import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Two.Data
import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Proofs
import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Boundary.Proofs

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- A second exactness step replaces existence of a boundary lift by the
vanishing of a concrete map to the next layer. This does not assert that
the obstruction vanishes on the full tensor of long layers. -/
theorem longLayerTwoComposition_exists_iff_obstruction_eq_zero
    (X Y Z : C) (s t : ℕ) :
    (∃ μ : adamsLongLayer H.unit (mappingObject X Y) 2 (by decide) s ⊗
        adamsLongLayer H.unit (mappingObject Y Z) 2 (by decide) t ⟶
      adamsLongLayer H.unit (mappingObject X Z) 2 (by decide) ((s : ℤ) + (t : ℤ)),
      μ ≫ adamsLongLayerProjection H.unit (mappingObject X Z) 2 (by decide)
        ((s : ℤ) + (t : ℤ)) = longLayerProjectedComposition H R X Y Z 2 (by decide) s t) ↔
      longLayerTwoCompositionObstruction H R X Y Z s t = 0 := by
  rw [longLayerComposition_exists_iff_boundaryLift]
  let T := adamsLayerTriangle H.unit (mappingObject X Z) (((s : ℤ) + (t : ℤ)) + 1)
  have hT := adamsLayerTriangle_distinguished H.unit (mappingObject X Z)
    (((s : ℤ) + (t : ℤ)) + 1)
  have hzero : T.mor₁ ≫ T.mor₂ = 0 := comp_distTriang_mor_zero₁₂ T hT
  constructor
  · rintro ⟨y, hy⟩
    unfold longLayerTwoCompositionObstruction
    rw [← hy, Category.assoc, ← Functor.map_comp]
    convert congrArg (fun f => y ≫ (shiftFunctor C (1 : ℤ)).map f) hzero using 1 <;>
      simp only [T, adamsLayerTriangle, Triangle.mk, Functor.map_zero, Limits.comp_zero] <;>
      congr 2
  · intro hz
    have hz' : longLayerCompositionBoundary H R X Y Z 2 (by decide) s t ≫
        ((shiftFunctor (Triangle C) (1 : ℤ)).obj T).mor₂ = 0 := by
      simpa [Triangle.shiftFunctor, longLayerTwoCompositionObstruction, T,
        adamsLayerTriangle, Triangle.mk, adamsLayerAt] using hz
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _
      (Triangle.shift_distinguished T hT (1 : ℤ)) _ hz'
    refine ⟨-y, ?_⟩
    have hy' : longLayerCompositionBoundary H R X Y Z 2 (by decide) s t =
        (-y) ≫ T.mor₁⟦(1 : ℤ)⟧' := by
      simpa [Triangle.shiftFunctor, Preadditive.comp_neg, Preadditive.neg_comp] using hy
    convert hy'.symm using 1
    congr 2

/-- In particular the concrete length-two obstruction is zero on two
tower representatives. This is weaker than global vanishing. -/
theorem longLayerTwoCompositionObstruction_ι (X Y Z : C) (s t : ℕ) :
    (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Y)
        (s : ℤ) ((s : ℤ) + 2) (by omega)) ⊗ₘ
      HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject Y Z)
        (t : ℤ) ((t : ℤ) + 2) (by omega))) ≫
        longLayerTwoCompositionObstruction H R X Y Z s t = 0 := by
  unfold longLayerTwoCompositionObstruction
  rw [← Category.assoc]
  erw [longLayerCompositionBoundary_ι H R X Y Z 2 (by decide) s t]
  exact Limits.zero_comp

end
end KIP126.Classical.Adams.Moss
