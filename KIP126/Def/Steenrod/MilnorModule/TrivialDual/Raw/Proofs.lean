module

public import KIP126.Def.Steenrod.MilnorModule.TrivialDual.Raw.Data

@[expose] public section

/-! Evaluation on the specified degree-line generator is an isomorphism
of the actual left modules, not an additional choice of coefficient object. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory MonoidalCategory

theorem trivialDualHom_action (t : ℤ) :
    (steenrod.X ◁ trivialDualHom t) ≫ (trivialAt t).a =
      (dualLeftModule (Ext.trivialAt t)).a ≫ trivialDualHom t := by
  exact (open KIP126.Core.Algebra KIP126.Algebra KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      classical
      have inclusion_leftUnitor (X : GrVect F2) (n : ℤ) :
        GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect F2)) X 0 n n (zero_add n) ≫
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
      have hco :
        (coactionComponent (Ext.trivialAt t) t 0).hom
          ((eqToHom (congrArg (Ext.trivialAt t).A (add_zero t).symm)).hom
            (GradedComodule.degreeLineGenerator F2 t)) =
            TensorProduct.tmul F2 (GradedComodule.degreeLineGenerator F2 t)
              (GradedDual.coaugmentationElement Coalgebra.coaugmentation) := by
        classical
        change (((ρ_ (GradedComodule.degreeLine F2 t)).inv (t+0) ≫
          GradedObject.Monoidal.tensorHom (𝟙 _) Coalgebra.coaugmentation.hom (t+0)) ≫
            GradedDual.tensorProjection _ _ t 0).hom _ = _
        change (((ρ_ (GradedComodule.degreeLine F2 t (t+0))).inv ≫
          (GradedComodule.degreeLine F2 t (t+0) ◁ GradedObject.Monoidal.tensorUnit₀.inv) ≫
            GradedObject.Monoidal.ιTensorObj _ _ (t+0) 0 (t+0) (add_zero _)) ≫ _ ≫ _).hom _ = _
        simp only [Category.assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
          GradedDual.tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc,
          add_zero, and_self, dite_true]
        change (eqToHom (congrArg (fun n => GradedComodule.degreeLine F2 t n ⊗ Coalgebra.dualSteenrod.X 0) (add_zero t))).hom
          (TensorProduct.tmul F2
            ((eqToHom (congrArg (GradedComodule.degreeLine F2 t) (add_zero t).symm)).hom
              (GradedComodule.degreeLineGenerator F2 t))
            (GradedDual.coaugmentationElement Coalgebra.coaugmentation)) = _
        have ht {i j : ℤ} (h : i = j) (x : GradedComodule.degreeLine F2 t i) (y : Coalgebra.dualSteenrod.X 0) :
            (eqToHom (congrArg (fun n => GradedComodule.degreeLine F2 t n ⊗ Coalgebra.dualSteenrod.X 0) h)).hom
              (TensorProduct.tmul F2 x y) =
            TensorProduct.tmul F2 ((eqToHom (congrArg (GradedComodule.degreeLine F2 t) h)).hom x) y := by
          subst j
          rfl
        rw [ht (add_zero t)]
        change TensorProduct.tmul F2
          (((eqToHom (congrArg (GradedComodule.degreeLine F2 t) (add_zero t))).hom)
            (((eqToHom (congrArg (GradedComodule.degreeLine F2 t) (add_zero t).symm))).hom
              (GradedComodule.degreeLineGenerator F2 t))) _ = _
        change TensorProduct.tmul F2
          ((eqToHom (congrArg (GradedComodule.degreeLine F2 t) (add_zero t).symm) ≫
            eqToHom (congrArg (GradedComodule.degreeLine F2 t) (add_zero t))).hom
              (GradedComodule.degreeLineGenerator F2 t)) _ = _
        simp only [eqToHom_trans, eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply]
      have dt (X : GrVect F2) {i j : ℤ} (h : i = j)
          (φ : Module.Dual F2 (X i)) (x : X j) :
          (show Module.Dual F2 (X j) from
            (eqToHom (congrArg (GradedDual.degreewiseDual X) h)).hom φ) x =
            φ ((eqToHom (congrArg X h.symm)).hom x) := by
        subst j
        rfl
      funext n
      by_cases hn : n = t
      · subst n
        apply GradedObject.Monoidal.tensorObj_ext
        intro i j hij
        by_cases hj : j = t
        · subst j
          have hi : i = 0 := by omega
          subst i
          change _ ≫ GradedObject.Monoidal.tensorHom (𝟙 _) (trivialDualHom t) t ≫
            GradedModule.trivialAction augmentation _ t = _ ≫ dualLeftAction _ t ≫ _
          simp only [GradedObject.Monoidal.ι_tensorHom_assoc,
            dualLeftAction, GradedObject.Monoidal.ι_tensorObjDesc_assoc]
          change _ ≫ _ ≫ GradedObject.Monoidal.tensorHom augmentation.hom (𝟙 (GradedComodule.degreeLine F2 t)) t ≫ (λ_ (GradedComodule.degreeLine F2 t)).hom t = _
          erw [GradedObject.Monoidal.ι_tensorHom_assoc, inclusion_leftUnitor]
          apply ModuleCat.hom_ext
          apply TensorProduct.ext
          apply LinearMap.ext
          intro a
          apply LinearMap.ext
          intro φ
          change Module.Dual F2 (Coalgebra.dualSteenrod.X 0) at a
          change Module.Dual F2 (GradedComodule.degreeLine F2 t t) at φ
          change ((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).hom.hom ((augmentation.hom 0).hom a)) •
            ((trivialDualHom t t).hom φ) =
            (trivialDualHom t t).hom
              ((eqToHom (congrArg (GradedDual.degreewiseDual (Ext.trivialAt t).A) (zero_add t))).hom
                ((dualLeftPairing (Ext.trivialAt t) 0 t).hom (TensorProduct.tmul F2 a φ)))
          have haug : (GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).hom.hom
              ((augmentation.hom 0).hom a) = a (GradedDual.coaugmentationElement Coalgebra.coaugmentation) := by
            change (GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).hom.hom
              ((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).inv.hom _) = _
            exact ModuleCat.hom_inv_apply _ _
          rw [haug]
          simp only [trivialDualHom, dite_true]
          apply (ModuleCat.mono_iff_injective (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom).mp inferInstance
          change (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom
            (a (GradedDual.coaugmentationElement Coalgebra.coaugmentation) •
              (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom
                (φ (GradedComodule.degreeLineGenerator F2 t))) =
            (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom
              ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom _)
          erw [map_smul, ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply]
          change a (GradedDual.coaugmentationElement Coalgebra.coaugmentation) *
            φ (GradedComodule.degreeLineGenerator F2 t) =
            (show Module.Dual F2 ((Ext.trivialAt t).A t) from
              (eqToHom (congrArg (GradedDual.degreewiseDual (Ext.trivialAt t).A) (zero_add t))).hom
                ((dualLeftPairing (Ext.trivialAt t) 0 t).hom (TensorProduct.tmul F2 a φ)))
              (GradedComodule.degreeLineGenerator F2 t)
          rw [dt (Ext.trivialAt t).A (zero_add t)]
          simp only [dualLeftPairing, ModuleCat.hom_comp, LinearMap.comp_apply]
          rw [dt (Ext.trivialAt t).A (add_comm t 0)]
          change a (GradedDual.coaugmentationElement Coalgebra.coaugmentation) *
              φ (GradedComodule.degreeLineGenerator F2 t) =
            TensorProduct.dualDistrib F2 (GradedComodule.degreeLine F2 t t) (Coalgebra.dualSteenrod.X 0)
              (TensorProduct.tmul F2 φ ((conjugation 0).hom a))
              ((coactionComponent (Ext.trivialAt t) t 0).hom
                ((eqToHom (congrArg (Ext.trivialAt t).A (zero_add t).symm) ≫
                  eqToHom (congrArg (Ext.trivialAt t).A (add_comm t 0).symm)).hom
                    (GradedComodule.degreeLineGenerator F2 t)))
          rw [eqToHom_trans, hco]
          change _ = φ (GradedComodule.degreeLineGenerator F2 t) *
            a ((Coalgebra.Antipode.map 0).hom (GradedDual.coaugmentationElement Coalgebra.coaugmentation))
          have hη : (Coalgebra.Antipode.map 0).hom
              (GradedDual.coaugmentationElement Coalgebra.coaugmentation) =
              GradedDual.coaugmentationElement Coalgebra.coaugmentation :=
            congrArg (fun f => f.hom
              ((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).inv.hom 1))
                (congrFun Coalgebra.Antipode.coaugmentation_map 0)
          rw [hη, mul_comm]
        · apply ModuleCat.hom_ext
          apply TensorProduct.ext
          apply LinearMap.ext
          intro a
          apply LinearMap.ext
          intro φ
          have hφ : φ = 0 := by
            apply LinearMap.ext
            intro x
            have hx : x = 0 := (ModuleCat.subsingleton_of_isZero
              (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) j hj).isZero).elim _ _
            subst x
            simp
          subst φ
          simp
      · exact (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero.eq_of_tgt _ _)

theorem trivialDualInv_action (t : ℤ) :
    (steenrod.X ◁ trivialDualInv t) ≫ (dualLeftModule (Ext.trivialAt t)).a =
      (trivialAt t).a ≫ trivialDualInv t := by
  exact (open KIP126.Core.Algebra KIP126.Algebra KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      have hleft : trivialDualHom t ≫ trivialDualInv t = 𝟙 (dualLeftModule (Ext.trivialAt t)).A := by
        classical
        funext n
        by_cases hn : n = t
        · subst n
          change trivialDualHom t t ≫ trivialDualInv t t = 𝟙 _
          simp only [trivialDualHom, trivialDualInv, dite_true]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro φ
          change Module.Dual F2 (GradedComodule.degreeLine F2 t t) at φ
          apply LinearMap.ext
          intro x
          change (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom
            ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom
              (φ (GradedComodule.degreeLineGenerator F2 t))) •
            (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom x = φ x
          erw [ModuleCat.hom_inv_apply]
          change φ (GradedComodule.degreeLineGenerator F2 t) *
            (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom x = φ x
          rw [mul_comm]
          rw [← smul_eq_mul, ← map_smul]
          congr 1
          change _ • (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom 1 = x
          erw [← map_smul, smul_eq_mul, mul_one, ModuleCat.inv_hom_apply]
        · have hz := (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro φ
          apply LinearMap.ext
          intro x
          have hx : x = 0 := by
            exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
          subst x
          simp
      have hright : trivialDualInv t ≫ trivialDualHom t = 𝟙 (trivialAt t).A := by
        classical
        funext n
        by_cases hn : n = t
        · subst n
          change trivialDualInv t t ≫ trivialDualHom t t = 𝟙 _
          simp only [trivialDualHom, trivialDualInv, dite_true]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          change (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom
            (((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom x) *
            (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom
              ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom 1)) = x
          erw [ModuleCat.hom_inv_apply, mul_one, ModuleCat.inv_hom_apply]
        · exact (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero.eq_of_tgt _ _
      suffices h : ((steenrod.X ◁ trivialDualInv t) ≫ (dualLeftModule (Ext.trivialAt t)).a) ≫ trivialDualHom t =
          ((trivialAt t).a ≫ trivialDualInv t) ≫ trivialDualHom t by
        have hh := congrArg (fun f => f ≫ trivialDualInv t) h
        simpa only [Category.assoc, hleft, Category.comp_id] using hh
      calc
        _ = (steenrod.X ◁ trivialDualInv t) ≫ ((steenrod.X ◁ trivialDualHom t) ≫ (trivialAt t).a) := by
          rw [Category.assoc, ← trivialDualHom_action]
        _ = (trivialAt t).a := by
          rw [← Category.assoc, ← whiskerLeft_comp, hright, whiskerLeft_id, Category.id_comp]
        _ = _ := by rw [Category.assoc, hright, Category.comp_id])

theorem trivialDualHom_inv (t : ℤ) :
    trivialDualHom t ≫ trivialDualInv t = 𝟙 (dualLeftModule (Ext.trivialAt t)).A := by
  exact (open KIP126.Core.Algebra KIP126.Algebra KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      classical
      funext n
      by_cases hn : n = t
      · subst n
        change trivialDualHom t t ≫ trivialDualInv t t = 𝟙 _
        simp only [trivialDualHom, trivialDualInv, dite_true]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual F2 (GradedComodule.degreeLine F2 t t) at φ
        apply LinearMap.ext
        intro x
        change (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom
          ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom
            (φ (GradedComodule.degreeLineGenerator F2 t))) •
          (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom x = φ x
        erw [ModuleCat.hom_inv_apply]
        change φ (GradedComodule.degreeLineGenerator F2 t) *
          (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom x = φ x
        rw [mul_comm]
        rw [← smul_eq_mul, ← map_smul]
        congr 1
        change _ • (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom 1 = x
        erw [← map_smul, smul_eq_mul, mul_one, ModuleCat.inv_hom_apply]
      · have hz := (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro x
        have hx : x = 0 := by
          exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
        subst x
        simp)

theorem trivialDualInv_hom (t : ℤ) :
    trivialDualInv t ≫ trivialDualHom t = 𝟙 (trivialAt t).A := by
  exact (open KIP126.Core.Algebra KIP126.Algebra KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      classical
      funext n
      by_cases hn : n = t
      · subst n
        change trivialDualInv t t ≫ trivialDualHom t t = 𝟙 _
        simp only [trivialDualHom, trivialDualInv, dite_true]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom
          (((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom x) *
          (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).hom.hom
            ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv.hom 1)) = x
        erw [ModuleCat.hom_inv_apply, mul_one, ModuleCat.inv_hom_apply]
      · exact (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero.eq_of_tgt _ _)

end KIP126.Steenrod.Milnor.Module
