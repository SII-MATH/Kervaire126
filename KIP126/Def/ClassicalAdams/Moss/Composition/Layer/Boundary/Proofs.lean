import KIP126.Def.ClassicalAdams.Moss.Composition.Layer.Proofs
import KIP126.Def.ClassicalAdams.Moss.Composition.Transition.Successor.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Step.Suspension.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Pairing.Restrictions.Proofs

namespace KIP126.Classical.Adams.Moss

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]

/-- The actual left successor of mapping-stage composition intertwines the
unit-fiber connecting maps. The tensor-suspension coherence is explicit and
the successor map is the previously constructed composition itself. -/
theorem stageComposition_δ_left {H : C} (unit : 𝟙_ C ⟶ H)
    (h : RightTensorSuspensionCompatibility (C := C))
    (X Y Z : C) (s t : ℕ) :
    (α_ H (mappingStage unit X Y s) (mappingStage unit Y Z t)).hom ≫
      H ◁ stageComposition unit X Y Z s t ≫
      (adamsFiberTriangle (adamsUnit unit (mappingStage unit X Z (t + s)))).mor₃ =
    ((adamsFiberTriangle (adamsUnit unit (mappingStage unit X Y s))).mor₃ ▷
      mappingStage unit Y Z t) ≫
      (Functor.commShiftIso (tensorRight (mappingStage unit Y Z t)) (1 : ℤ)).hom.app
        (mappingStage unit X Y (s + 1)) ≫
      (stageComposition unit X Y Z (s + 1) t)⟦(1 : ℤ)⟧' := by
  have hnext :
      ((adamsFiberTensorIso unit (mappingStage unit X Y s)).hom ▷
        mappingStage unit Y Z t) ≫
        (α_ (fiber unit) (mappingStage unit X Y s) (mappingStage unit Y Z t)).hom ≫
        fiber unit ◁ stageComposition unit X Y Z s t ≫
        (adamsFiberTensorIso unit (mappingStage unit X Z (t + s))).inv =
      stageComposition unit X Y Z (s + 1) t := by
    have hc := congrArg (fun f => f ≫
      (adamsFiberTensorIso unit (mappingStage unit X Z (t + s))).inv)
        (stageComposition_succ_comparison unit X Y Z s t)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc.symm
  exact (adamsFiberTensorIso_pairing_δ unit h
    (stageComposition unit X Y Z s t)).trans
      (congrArg (fun f =>
        ((adamsFiberTriangle (adamsUnit unit (mappingStage unit X Y s))).mor₃ ▷
          mappingStage unit Y Z t) ≫
          (Functor.commShiftIso (tensorRight (mappingStage unit Y Z t)) (1 : ℤ)).hom.app
            (mappingStage unit X Y (s + 1)) ≫ f⟦(1 : ℤ)⟧') hnext)

variable (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Restricting the second input to its actual tower image removes the
coefficient multiplication, in the existing layer coordinates. -/
theorem layerComposition_ι_right_comparison (X Y Z : C) (s t : ℕ) :
    (((adamsLayerIso H.unit (mappingObject X Y) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
      layerComposition H R X Y Z s t) ≫
      (adamsLayerIso H.unit (mappingObject X Z) (t + s)).hom =
    (α_ H.HF2 (mappingStage H.unit X Y s) (mappingStage H.unit Y Z t)).hom ≫
      H.HF2 ◁ stageComposition H.unit X Y Z s t := by
  have hι : (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂ ≫
      (adamsLayerIso H.unit (mappingObject Y Z) t).hom =
      adamsUnit H.unit (mappingStage H.unit Y Z t) :=
    adamsLayerIso_ι H.unit (mappingObject Y Z) t
  have htensor :
      ((adamsLayerIso H.unit (mappingObject X Y) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
      ((adamsLayerIso H.unit (mappingObject X Y) s).hom ⊗ₘ
        (adamsLayerIso H.unit (mappingObject Y Z) t).hom) =
      𝟙 (H.HF2 ⊗ mappingStage H.unit X Y s) ⊗ₘ
        adamsUnit H.unit (mappingStage H.unit Y Z t) :=
    (tensorHom_comp_tensorHom _ _ _ _).trans
      (congrArg₂ (fun f g => f ⊗ₘ g) (Iso.inv_hom_id _) hι)
  erw [Category.assoc, layerComposition_comparison, ← Category.assoc, htensor]
  rw [id_tensorHom]
  exact mod2CoefficientPairing_unit_right H R _

/-- In coefficient coordinates, the one-sided layer boundary carries the
minus sign prescribed by the positive fiber-inclusion convention. -/
theorem layerComposition_ι_right_δ_comparison
    (h : RightTensorSuspensionCompatibility (C := C))
    (X Y Z : C) (s t : ℕ) :
    (((adamsLayerIso H.unit (mappingObject X Y) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
      layerComposition H R X Y Z s t) ≫
      (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₃ =
    -(((adamsFiberTriangle (adamsUnit H.unit (mappingStage H.unit X Y s))).mor₃ ▷
        mappingStage H.unit Y Z t) ≫
      (Functor.commShiftIso (tensorRight (mappingStage H.unit Y Z t)) (1 : ℤ)).hom.app
        (mappingStage H.unit X Y (s + 1)) ≫
      (stageComposition H.unit X Y Z (s + 1) t)⟦(1 : ℤ)⟧') := by
  have hd := adamsLayerIso_δ H.unit (mappingObject X Z) (t + s)
  have hp := layerComposition_ι_right_comparison H R X Y Z s t
  have hb := stageComposition_δ_left H.unit h X Y Z s t
  exact (congrArg (fun f => (((adamsLayerIso H.unit (mappingObject X Y) s).inv ⊗ₘ
      (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
      layerComposition H R X Y Z s t) ≫ f) hd).trans
    ((Preadditive.comp_neg _ _).trans (congrArg (fun f => -f)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫
          (adamsFiberTriangle (adamsUnit H.unit (mappingStage H.unit X Z (t + s)))).mor₃)
            hp).trans ((Category.assoc _ _ _).trans hb)))))

variable [MonoidalPreadditive C]

/-- The specified mapping-object layer composition satisfies a genuine
one-sided connecting-map identity. The right input lies in its tower image;
the left boundary is followed by the actual left successor composition.
This does not assert the other boundary formula or a pagewise Leibniz law. -/
theorem layerComposition_ι_right_δ
    (h : RightTensorSuspensionCompatibility (C := C))
    (X Y Z : C) (s t : ℕ) :
    (adamsLayerAt H.unit (mappingObject X Y) s ◁
        (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
      layerComposition H R X Y Z s t ≫
      (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₃ =
    ((adamsLayerTriangle H.unit (mappingObject X Y) s).mor₃ ▷
        mappingStage H.unit Y Z t) ≫
      (Functor.commShiftIso (tensorRight (mappingStage H.unit Y Z t)) (1 : ℤ)).hom.app
        (mappingStage H.unit X Y (s + 1)) ≫
      (stageComposition H.unit X Y Z (s + 1) t)⟦(1 : ℤ)⟧' := by
  have hd : (adamsLayerIso H.unit (mappingObject X Y) s).inv ≫
      (adamsLayerTriangle H.unit (mappingObject X Y) s).mor₃ =
      -(adamsFiberTriangle (adamsUnit H.unit (mappingStage H.unit X Y s))).mor₃ := by
    exact (congrArg (fun f => (adamsLayerIso H.unit (mappingObject X Y) s).inv ≫ f)
      (adamsLayerIso_δ H.unit (mappingObject X Y) s)).trans
        ((Preadditive.comp_neg _ _).trans
          (congrArg (fun f => -f) (Iso.inv_hom_id_assoc _ _)))
  have ht : ((adamsLayerIso H.unit (mappingObject X Y) s).inv ▷ mappingStage H.unit Y Z t) ≫
      ((adamsLayerTriangle H.unit (mappingObject X Y) s).mor₃ ▷ mappingStage H.unit Y Z t) =
      -((adamsFiberTriangle (adamsUnit H.unit (mappingStage H.unit X Y s))).mor₃ ▷
        mappingStage H.unit Y Z t) :=
    (comp_whiskerRight _ _ _).symm.trans
      ((congrArg (fun f => f ▷ mappingStage H.unit Y Z t) hd).trans
        ((tensorRight (mappingStage H.unit Y Z t)).map_neg))
  have hr : ((adamsLayerIso H.unit (mappingObject X Y) s).inv ▷ mappingStage H.unit Y Z t) ≫
      (((adamsLayerTriangle H.unit (mappingObject X Y) s).mor₃ ▷ mappingStage H.unit Y Z t) ≫
        (Functor.commShiftIso (tensorRight (mappingStage H.unit Y Z t)) (1 : ℤ)).hom.app
          (mappingStage H.unit X Y (s + 1)) ≫
        (stageComposition H.unit X Y Z (s + 1) t)⟦(1 : ℤ)⟧') =
      -(((adamsFiberTriangle (adamsUnit H.unit (mappingStage H.unit X Y s))).mor₃ ▷
          mappingStage H.unit Y Z t) ≫
        (Functor.commShiftIso (tensorRight (mappingStage H.unit Y Z t)) (1 : ℤ)).hom.app
          (mappingStage H.unit X Y (s + 1)) ≫
        (stageComposition H.unit X Y Z (s + 1) t)⟦(1 : ℤ)⟧') :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫
        (Functor.commShiftIso (tensorRight (mappingStage H.unit Y Z t)) (1 : ℤ)).hom.app
          (mappingStage H.unit X Y (s + 1)) ≫
        (stageComposition H.unit X Y Z (s + 1) t)⟦(1 : ℤ)⟧') ht).trans
          (Preadditive.neg_comp _ _))
  apply (cancel_epi
    ((adamsLayerIso H.unit (mappingObject X Y) s).inv ▷ mappingStage H.unit Y Z t)).mp
  have hl : ((adamsLayerIso H.unit (mappingObject X Y) s).inv ▷ mappingStage H.unit Y Z t) ≫
      ((adamsLayerAt H.unit (mappingObject X Y) s ◁
          (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
        layerComposition H R X Y Z s t ≫
        (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₃) =
      (((adamsLayerIso H.unit (mappingObject X Y) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (mappingObject Y Z) t).mor₂) ≫
        layerComposition H R X Y Z s t) ≫
        (adamsLayerTriangle H.unit (mappingObject X Z) ((t + s : ℕ) : ℤ)).mor₃ := by
    simp only [tensorHom_def, Category.assoc]
    rfl
  exact hl.trans ((layerComposition_ι_right_δ_comparison H R h X Y Z s t).trans hr.symm)

end
end KIP126.Classical.Adams.Moss
