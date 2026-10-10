import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Data
import KIP126.Def.ClassicalAdams.Moss.Composition.Layer.Proofs
import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Proofs
import KIP126.Def.StableHomotopy.Context.Mapping.Data

/-! Restrictions of the actual composition boundary to tower representatives.
The two factorizations below are consequences of exactness, not additional
boundary hypotheses. They do not assert a two-term formula on the full tensor
of long layers: the compatibility needed to glue them remains separate. -/

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

omit [MonoidalClosed C] [BraidedCategory C]
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] in
private theorem longProjection_ι (A : C) (r : ℕ) (hr : 1 ≤ r) (s : ℤ) :
    HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit A s (s + r) (by omega)) ≫
        adamsLongLayerProjection H.unit A r hr s =
      (adamsLayerTriangle H.unit A s).mor₂ :=
  cofiberFactorizationMap_ι _ _ _ _

/-- On the two actual tower images the prescribed long-layer projection is
the same stage composition followed by the target layer inclusion. -/
theorem longLayerProjectedComposition_ι (X Y Z : C)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Y)
        (s : ℤ) ((s : ℤ) + r) (by omega)) ⊗ₘ
      HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject Y Z)
        (t : ℤ) ((t : ℤ) + r) (by omega))) ≫
        longLayerProjectedComposition H R X Y Z r hr s t =
      stageComposition H.unit X Y Z s t ≫
        (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₂ ≫
          eqToHom (congrArg (adamsLayerAt H.unit (mappingObject X Z)) (by omega :
            ((t + s : ℕ) : ℤ) = (s : ℤ) + (t : ℤ))) := by
  unfold longLayerProjectedComposition layerCompositionOrdered
  rw [← Category.assoc, tensorHom_comp_tensorHom, longProjection_ι,
    longProjection_ι, ← Category.assoc]
  erw [layerComposition_ι]
  exact Category.assoc _ _ _

omit [MonoidalClosed C] [BraidedCategory C]
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] in
private theorem layerInclusion_transport_boundary (A : C) (a b : ℤ) (h : a = b) :
    (adamsLayerTriangle H.unit A a).mor₂ ≫
        eqToHom (congrArg (adamsLayerAt H.unit A) h) ≫
          (adamsLayerTriangle H.unit A b).mor₃ = 0 := by
  subst b
  change (adamsLayerTriangle H.unit A a).mor₂ ≫ 𝟙 _ ≫
    (adamsLayerTriangle H.unit A a).mor₃ = 0
  rw [Category.id_comp]
  exact comp_distTriang_mor_zero₂₃ _ (adamsLayerTriangle_distinguished H.unit A a)

/-- The composition boundary vanishes on two tower representatives. This is
a consequence of the actual coefficient unit and the target cofiber triangle. -/
theorem longLayerCompositionBoundary_ι (X Y Z : C)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Y)
        (s : ℤ) ((s : ℤ) + r) (by omega)) ⊗ₘ
      HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject Y Z)
        (t : ℤ) ((t : ℤ) + r) (by omega))) ≫
        longLayerCompositionBoundary H R X Y Z r hr s t = 0 := by
  unfold longLayerCompositionBoundary
  rw [← Category.assoc, longLayerProjectedComposition_ι]
  simp only [Category.assoc]
  change stageComposition H.unit X Y Z s t ≫
    ((adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₂ ≫
      eqToHom (congrArg (adamsLayerAt H.unit (mappingObject X Z))
        (by omega : ((t + s : ℕ) : ℤ) = (s : ℤ) + (t : ℤ))) ≫
      (adamsLayerTriangle H.unit (mappingObject X Z)
        ((s : ℤ) + (t : ℤ))).mor₃) = 0
  rw [layerInclusion_transport_boundary H (mappingObject X Z)
    ((t + s : ℕ) : ℤ) ((s : ℤ) + (t : ℤ)) (by omega), Limits.comp_zero]

/-- With the right input restricted to its tower, the boundary factors
through the actual left long-cofiber connecting map. The suspension tensor
comparison is retained explicitly. No factor is postulated as input. -/
theorem longLayerCompositionBoundary_rightTower_factors (X Y Z : C)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    ∃ a : (adamsTowerAt H.unit (mappingObject X Y) ((s : ℤ) + r) ⊗
        adamsTowerAt H.unit (mappingObject Y Z) t)⟦(1 : ℤ)⟧ ⟶
      (adamsTowerAt H.unit (mappingObject X Z)
        (((s : ℤ) + (t : ℤ)) + 1))⟦(1 : ℤ)⟧,
      (adamsLongLayer H.unit (mappingObject X Y) r hr s ◁
          HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject Y Z)
            (t : ℤ) ((t : ℤ) + r) (by omega))) ≫
          longLayerCompositionBoundary H R X Y Z r hr s t =
        (HasFunctorialCofiber.cofibδ (adamsTowerMapAt H.unit (mappingObject X Y)
            (s : ℤ) ((s : ℤ) + r) (by omega)) ▷
          adamsTowerAt H.unit (mappingObject Y Z) t) ≫
          (Functor.commShiftIso (tensorRight (adamsTowerAt H.unit (mappingObject Y Z) t))
            (1 : ℤ)).hom.app (adamsTowerAt H.unit (mappingObject X Y) ((s : ℤ) + r)) ≫ a := by
  let T := (HoCofiberSequence.ofMorphism (adamsTowerMapAt H.unit (mappingObject X Y)
    (s : ℤ) ((s : ℤ) + r) (by omega))).map
      (tensorRight (adamsTowerAt H.unit (mappingObject Y Z) t))
  let b := (adamsLongLayer H.unit (mappingObject X Y) r hr s ◁
    HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject Y Z)
      (t : ℤ) ((t : ℤ) + r) (by omega))) ≫
      longLayerCompositionBoundary H R X Y Z r hr s t
  have hz : T.g ≫ b = 0 := by
    change (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Y)
        (s : ℤ) ((s : ℤ) + r) (by omega)) ▷
      adamsTowerAt H.unit (mappingObject Y Z) t) ≫ _ = 0
    simpa only [b, tensorHom_def, Category.assoc] using
      longLayerCompositionBoundary_ι H R X Y Z r hr s t
  obtain ⟨a, ha⟩ := Triangle.yoneda_exact₃ (Triangle.mk T.f T.g T.h) T.distinguished b hz
  refine ⟨a, ?_⟩
  change b = ((HasFunctorialCofiber.cofibδ
    (adamsTowerMapAt H.unit (mappingObject X Y) (s : ℤ) ((s : ℤ) + r) (by omega)) ▷
      adamsTowerAt H.unit (mappingObject Y Z) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTowerAt H.unit (mappingObject Y Z) t))
          (1 : ℤ)).hom.app (adamsTowerAt H.unit (mappingObject X Y) ((s : ℤ) + r))) ≫ a at ha
  exact ha.trans (Category.assoc _ _ _)

variable [∀ A : C, (tensorLeft A).CommShift ℤ]
  [∀ A : C, (tensorLeft A).IsTriangulated]

/-- The other restriction factors through the right long-cofiber boundary.
This does not identify its factor with an ordered successor composition. -/
theorem longLayerCompositionBoundary_leftTower_factors (X Y Z : C)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    ∃ b : (adamsTowerAt H.unit (mappingObject X Y) s ⊗
        adamsTowerAt H.unit (mappingObject Y Z) ((t : ℤ) + r))⟦(1 : ℤ)⟧ ⟶
      (adamsTowerAt H.unit (mappingObject X Z)
        (((s : ℤ) + (t : ℤ)) + 1))⟦(1 : ℤ)⟧,
      (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Y)
          (s : ℤ) ((s : ℤ) + r) (by omega)) ▷
        adamsLongLayer H.unit (mappingObject Y Z) r hr t) ≫
          longLayerCompositionBoundary H R X Y Z r hr s t =
        (adamsTowerAt H.unit (mappingObject X Y) s ◁
          HasFunctorialCofiber.cofibδ (adamsTowerMapAt H.unit (mappingObject Y Z)
            (t : ℤ) ((t : ℤ) + r) (by omega))) ≫
          (Functor.commShiftIso (tensorLeft (adamsTowerAt H.unit (mappingObject X Y) s))
            (1 : ℤ)).hom.app (adamsTowerAt H.unit (mappingObject Y Z) ((t : ℤ) + r)) ≫ b := by
  let T := (HoCofiberSequence.ofMorphism (adamsTowerMapAt H.unit (mappingObject Y Z)
    (t : ℤ) ((t : ℤ) + r) (by omega))).map
      (tensorLeft (adamsTowerAt H.unit (mappingObject X Y) s))
  let a := (HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject X Y)
    (s : ℤ) ((s : ℤ) + r) (by omega)) ▷
      adamsLongLayer H.unit (mappingObject Y Z) r hr t) ≫
        longLayerCompositionBoundary H R X Y Z r hr s t
  have hz : T.g ≫ a = 0 := by
    change (adamsTowerAt H.unit (mappingObject X Y) s ◁
      HasFunctorialCofiber.cofibι (adamsTowerMapAt H.unit (mappingObject Y Z)
        (t : ℤ) ((t : ℤ) + r) (by omega))) ≫ _ = 0
    simpa only [a, tensorHom_def', Category.assoc] using
      longLayerCompositionBoundary_ι H R X Y Z r hr s t
  obtain ⟨b, hb⟩ := Triangle.yoneda_exact₃ (Triangle.mk T.f T.g T.h) T.distinguished a hz
  refine ⟨b, ?_⟩
  change a = ((adamsTowerAt H.unit (mappingObject X Y) s ◁
    HasFunctorialCofiber.cofibδ (adamsTowerMapAt H.unit (mappingObject Y Z)
      (t : ℤ) ((t : ℤ) + r) (by omega))) ≫
        (Functor.commShiftIso (tensorLeft (adamsTowerAt H.unit (mappingObject X Y) s))
          (1 : ℤ)).hom.app (adamsTowerAt H.unit (mappingObject Y Z) ((t : ℤ) + r))) ≫ b at hb
  exact hb.trans (Category.assoc _ _ _)

end
end KIP126.Classical.Adams.Moss
