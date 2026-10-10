import KIP126.Def.Algebra.GradedDual.Augmentation.Raw.Data

/-! The prescribed evaluation preserves the convolution unit and product
because the specified coaugmentation is a comonoid morphism. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace
open scoped MonObj

universe u
variable {K : Type u} [Field K] {C : Comon (GrVect K)}

theorem convolutionAugmentation_unit (coaug : GradedComodule.Coaugmentation C) :
    η[(convolutionAlgebra C).X] ≫ convolutionAugmentationMap coaug = η[𝟙_ (GrVect K)] := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    let e : (𝟙_ (GrVect K)) 0 ≅ ModuleCat.of K K := GradedObject.Monoidal.tensorUnit₀
    have hc : coaug.hom 0 ≫ (ComonObj.counit (X := C.X)) 0 = 𝟙 _ := by
      exact congrFun (IsComonHom.hom_counit coaug.hom) 0
    have he : (scalarCounit C).hom (coaugmentationElement coaug) = 1 := by
      change (e.inv ≫ (coaug.hom 0 ≫ (ComonObj.counit (X := C.X)) 0) ≫ e.hom).hom (1 : K) = 1
      erw [hc]
      rfl
    funext n
    by_cases hn : n = 0
    · subst n
      change convolutionUnit C 0 ≫ convolutionAugmentationMap coaug 0 = 𝟙 _
      dsimp only [convolutionUnit, convolutionAugmentationMap]
      simp only [dite_true]
      apply (cancel_epi e.inv).1
      apply (cancel_mono e.hom).1
      dsimp only [e]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      dsimp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      erw [Module.Dual.eval_apply, LinearMap.dualMap_apply, LinearMap.toSpanSingleton_apply]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, he, smul_eq_mul, mul_one]
      rfl
    · exact (GradedObject.Monoidal.isInitialTensorUnitApply n hn).hom_ext _ _

theorem convolutionAugmentation_mul (coaug : GradedComodule.Coaugmentation C) :
    μ[(convolutionAlgebra C).X] ≫ convolutionAugmentationMap coaug =
      (convolutionAugmentationMap coaug ⊗ₘ convolutionAugmentationMap coaug) ≫
        μ[𝟙_ (GrVect K)] := by
  set_option backward.isDefEq.respectTransparency false in
    have inclusion_leftUnitor (X : GrVect K) (n : ℤ) :
      GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect K)) X 0 n n (zero_add n) ≫
        (λ_ X).hom n = (GradedObject.Monoidal.tensorUnit₀.hom ▷ X n) ≫ (λ_ (X n)).hom := by
      apply (cancel_mono ((λ_ X).inv n)).1
      simp only [Category.assoc]
      rw [show (λ_ X).hom n ≫ (λ_ X).inv n = 𝟙 _ from congrFun (λ_ X).hom_inv_id n]
      erw [Category.comp_id]
      change _ = (GradedObject.Monoidal.tensorUnit₀.hom ▷ X n) ≫ (λ_ (X n)).hom ≫
        (λ_ (X n)).inv ≫ (GradedObject.Monoidal.tensorUnit₀.inv ▷ X n) ≫
          GradedObject.Monoidal.ιTensorObj _ _ _ _ _ _
      simp only [Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc]
      rfl
    have dual_transport (X : GrVect K) {i j : ℤ} (h : i = j)
      (φ : Module.Dual K (X i)) (x : X j) :
      (show Module.Dual K (X j) from ((eqToHom (congrArg (degreewiseDual X) h)).hom φ)) x =
        φ ((eqToHom (congrArg X h.symm)).hom x) := by
      subst j
      rfl
    have coaugmentation_groupLike (coaug : GradedComodule.Coaugmentation C) :
      ((ComonObj.comul (X := C.X)) 0).hom (coaugmentationElement coaug) =
        (GradedObject.Monoidal.ιTensorObj C.X C.X 0 0 0 (zero_add 0)).hom
          (TensorProduct.tmul K (coaugmentationElement coaug) (coaugmentationElement coaug)) := by
      have h : coaug.hom 0 ≫ (ComonObj.comul (X := C.X)) 0 =
          (λ_ (𝟙_ (GrVect K))).inv 0 ≫ GradedObject.Monoidal.tensorHom coaug.hom coaug.hom 0 :=
        congrFun (IsComonHom.hom_comul coaug.hom) 0
      let e : (𝟙_ (GrVect K)) 0 ≅ ModuleCat.of K K := GradedObject.Monoidal.tensorUnit₀
      change (coaug.hom 0 ≫ (ComonObj.comul (X := C.X)) 0).hom (e.inv.hom 1) = _
      rw [h]
      change (((λ_ ((𝟙_ (GrVect K)) 0)).inv ≫
        (e.inv ▷ (𝟙_ (GrVect K)) 0) ≫
          GradedObject.Monoidal.ιTensorObj _ _ 0 0 0 (zero_add 0)) ≫ _).hom _ = _
      simp only [Category.assoc, GradedObject.Monoidal.ι_tensorHom, ModuleCat.hom_comp,
        LinearMap.comp_apply]
      erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply (R := K) (M := (𝟙_ (GrVect K)) 0),
        ModuleCat.MonoidalCategory.tensorHom_tmul (R := K) (coaug.hom 0) (coaug.hom 0)]
      rfl
    have component_coaugmentation_zero (coaug : GradedComodule.Coaugmentation C)
      (i j : ℤ) (hij : i + j = 0) (hi : i ≠ 0) :
      (comultiplicationComponent C i j).hom
        ((eqToHom (congrArg C.X hij.symm)).hom (coaugmentationElement coaug)) = 0 := by
      classical
      have ht (X Y : GrVect K) (f : X ⟶ Y) (a b : ℤ) (h : a = b) :
          eqToHom (congrArg X h) ≫ f b = f a ≫ eqToHom (congrArg Y h) := by
        subst b
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      have hin (X Y : GrVect K) (n : ℤ) (h : 0 + 0 = n) :
          GradedObject.Monoidal.ιTensorObj X Y 0 0 (0 + 0) rfl ≫ eqToHom (congrArg (show GrVect K from X ⊗ Y) h) =
            GradedObject.Monoidal.ιTensorObj X Y 0 0 n h := by
        subst n
        simp only [eqToHom_refl, Category.comp_id]
      change (eqToHom (congrArg C.X hij.symm) ≫
        (ComonObj.comul (X := C.X)) (i + j) ≫ tensorProjection C.X C.X i j).hom
          (coaugmentationElement coaug) = 0
      rw [← Category.assoc, ht C.X (C.X ⊗ C.X) (ComonObj.comul (X := C.X)) 0 (i + j) hij.symm]
      change (tensorProjection C.X C.X i j).hom
        ((eqToHom (congrArg (show GrVect K from C.X ⊗ C.X) hij.symm)).hom
          (((ComonObj.comul (X := C.X)) 0).hom (coaugmentationElement coaug))) = 0
      rw [coaugmentation_groupLike]
      change ((GradedObject.Monoidal.ιTensorObj C.X C.X 0 0 0 (zero_add 0) ≫
        eqToHom (congrArg (show GrVect K from C.X ⊗ C.X) hij.symm)) ≫ tensorProjection C.X C.X i j).hom _ = 0
      erw [hin C.X C.X (i + j) ((zero_add 0).trans hij.symm), tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc]
      have hn : ¬ (0 = i ∧ 0 = j) := fun h => hi h.1.symm
      simp only [hn, dite_false, ModuleCat.hom_zero, LinearMap.zero_apply]
    classical
    funext n
    by_cases hn : n = 0
    · subst n
      change convolutionMultiplication C 0 ≫ convolutionAugmentationMap coaug 0 =
        GradedObject.Monoidal.tensorHom (convolutionAugmentationMap coaug)
          (convolutionAugmentationMap coaug) 0 ≫ (λ_ (𝟙_ (GrVect K))).hom 0
      apply GradedObject.Monoidal.tensorObj_ext
      intro i j hij
      simp only [convolutionMultiplication, GradedObject.Monoidal.ι_tensorObjDesc_assoc,
        GradedObject.Monoidal.ι_tensorHom_assoc]
      by_cases hi : i = 0
      · subst i
        have hj : j = 0 := by simpa using hij
        subst j
        simp only [convolutionAugmentationMap, dite_true, eqToHom_refl, Category.comp_id]
        apply ModuleCat.hom_ext
        refine TensorProduct.ext (LinearMap.ext fun φ => LinearMap.ext fun ψ => ?_)
        change Module.Dual K (C.X 0) at φ ψ
        erw [inclusion_leftUnitor (𝟙_ (GrVect K)) 0]
        change TensorProduct.dualDistrib K (C.X 0) (C.X 0) (TensorProduct.tmul K φ ψ)
          ((comultiplicationComponent C 0 0).hom (coaugmentationElement coaug)) = _
        have hc : (comultiplicationComponent C 0 0).hom (coaugmentationElement coaug) =
            TensorProduct.tmul K (coaugmentationElement coaug) (coaugmentationElement coaug) := by
          change (tensorProjection C.X C.X 0 0).hom
            (((ComonObj.comul (X := C.X)) 0).hom (coaugmentationElement coaug)) = _
          rw [coaugmentation_groupLike]
          change (GradedObject.Monoidal.ιTensorObj C.X C.X 0 0 0 (zero_add 0) ≫
            tensorProjection C.X C.X 0 0).hom _ = _
          simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc, and_self, dite_true, eqToHom_refl]
          rfl
        rw [hc, TensorProduct.dualDistrib_apply]
        rfl
      · have hai : convolutionAugmentationMap coaug i = 0 := by
          simp only [convolutionAugmentationMap, hi, dite_false]
        rw [hai]
        simp only [MonoidalPreadditive.zero_tensor, CategoryTheory.Limits.zero_comp]
        apply ModuleCat.hom_ext
        refine TensorProduct.ext (LinearMap.ext fun φ => LinearMap.ext fun ψ => ?_)
        change Module.Dual K (C.X i) at φ
        change Module.Dual K (C.X j) at ψ
        change (convolutionAugmentationMap coaug 0).hom
          ((eqToHom (congrArg (degreewiseDual C.X) hij)).hom
            ((convolutionPairing C i j).hom (TensorProduct.tmul K φ ψ))) = 0
        simp only [convolutionAugmentationMap, dite_true, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
          LinearMap.comp_apply]
        change (show Module.Dual K (C.X 0) from
          (eqToHom (congrArg (degreewiseDual C.X) hij)).hom
            ((convolutionPairing C i j).hom (TensorProduct.tmul K φ ψ))) (coaugmentationElement coaug) = 0
        erw [dual_transport C.X hij]
        change TensorProduct.dualDistrib K (C.X i) (C.X j) (TensorProduct.tmul K φ ψ)
            ((comultiplicationComponent C i j).hom
              ((eqToHom (congrArg C.X hij.symm)).hom (coaugmentationElement coaug))) = 0
        rw [component_coaugmentation_zero coaug i j hij hi, map_zero]
    · exact (GradedObject.Monoidal.isInitialTensorUnitApply n hn).isZero.eq_of_tgt _ _

end KIP126.Algebra.GradedDual
