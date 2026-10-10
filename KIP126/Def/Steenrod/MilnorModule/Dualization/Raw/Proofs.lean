import KIP126.Def.Steenrod.MilnorModule.Dualization.Raw.Data

/-! Precise properties of the prescribed transpose-conjugation action.
These statements do not assert an equivalence of unrestricted categories. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory MonoidalCategory KIP126.Algebra
open scoped MonObj

theorem conjugation_unit : η[steenrod.X] ≫ conjugation = η[steenrod.X] := by
  funext n
  change GradedDual.convolutionUnit Coalgebra.dualSteenrod n ≫ conjugation n =
    GradedDual.convolutionUnit Coalgebra.dualSteenrod n
  by_cases hn : n = 0
  · subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    apply LinearMap.ext
    intro x
    change (show Module.Dual KIP126.Core.Algebra.F2 (Coalgebra.Carrier 0) from
      (GradedDual.convolutionUnit Coalgebra.dualSteenrod 0).hom r)
      ((Coalgebra.Antipode.map 0).hom x) =
      (show Module.Dual KIP126.Core.Algebra.F2 (Coalgebra.Carrier 0) from
        (GradedDual.convolutionUnit Coalgebra.dualSteenrod 0).hom r) x
    have h := congrArg (fun h => h.hom x) (congrFun Coalgebra.Antipode.map_counit 0)
    change (Coalgebra.counit 0).hom ((Coalgebra.Antipode.map 0).hom x) =
      (Coalgebra.counit 0).hom x at h
    change (((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat KIP126.Core.Algebra.F2) (I := ℤ)).hom.hom r : KIP126.Core.Algebra.F2)) • ((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat KIP126.Core.Algebra.F2) (I := ℤ)).hom.hom
      ((Coalgebra.counit 0).hom ((Coalgebra.Antipode.map 0).hom x))) =
      (((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat KIP126.Core.Algebra.F2) (I := ℤ)).hom.hom r : KIP126.Core.Algebra.F2)) • ((GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat KIP126.Core.Algebra.F2) (I := ℤ)).hom.hom ((Coalgebra.counit 0).hom x))
    rw [h]
  · simp only [GradedDual.convolutionUnit, hn, dite_false, Limits.zero_comp]
    rfl

/-- Transposing anti-comultiplicativity reverses the convolution factors. -/
theorem conjugation_mul :
    μ[steenrod.X] ≫ conjugation =
      (conjugation ⊗ₘ conjugation) ≫ (β_ steenrod.X steenrod.X).hom ≫ μ[steenrod.X] := by
  exact (open KIP126.Core.Algebra KIP126.Algebra.GradedVectorSpace KIP126.Algebra.GradedDual GradedObject.Monoidal in by
    set_option backward.isDefEq.respectTransparency false in
      have hs (i j : ℤ) :
          Coalgebra.Antipode.map (i+j) ≫ comultiplicationComponent Coalgebra.dualSteenrod i j =
          eqToHom (congrArg Coalgebra.dualSteenrod.X (add_comm i j)) ≫
            comultiplicationComponent Coalgebra.dualSteenrod j i ≫
              (Coalgebra.Antipode.map j ⊗ₘ Coalgebra.Antipode.map i) ≫
                (β_ (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X i)).hom := by
        have hb (X Y : GrVect F2) (i j : ℤ) :
            (β_ X Y).hom (i+j) ≫ tensorProjection Y X i j =
            eqToHom (congrArg (show GrVect F2 from X ⊗ Y) (add_comm i j)) ≫
              tensorProjection X Y j i ≫ (β_ (X j) (Y i)).hom := by
          classical
          have ht (A B : GrVect F2) (a b n m : ℤ) (h : a+b=n) (e : n=m)
              {T : ModuleCat F2} (g : (show GrVect F2 from A ⊗ B) m ⟶ T) :
              ιTensorObj A B a b n h ≫ eqToHom (congrArg (show GrVect F2 from A ⊗ B) e) ≫ g =
                ιTensorObj A B a b m (h.trans e) ≫ g := by
            subst m
            simp only [eqToHom_refl, Category.id_comp]
          apply tensorObj_ext
          intro a b hab
          change _ ≫ tensorObjDesc (fun r s h => (β_ (X r) (Y s)).hom ≫ ιTensorObj Y X s r (i+j) _) ≫ _ = _
          simp only [ι_tensorObjDesc_assoc, Category.assoc]
          erw [ht X Y a b _ _ hab (add_comm i j) _]
          simp only [tensorProjection, ι_tensorObjDesc, ι_tensorObjDesc_assoc]
          by_cases h : a=j ∧ b=i
          · rcases h with ⟨rfl,rfl⟩
            simp only [and_self, dite_true, eqToHom_refl, Category.id_comp, Category.comp_id]
          · have h' : ¬(b=i ∧ a=j) := by tauto
            simp only [h,h',dite_false,Limits.zero_comp,Limits.comp_zero]

        have hp (X Y X' Y' : GrVect F2) (g : X ⟶ X') (h : Y ⟶ Y') (i j : ℤ) :
            GradedObject.Monoidal.tensorHom g h (i+j) ≫ tensorProjection X' Y' i j =
            tensorProjection X Y i j ≫ (g i ⊗ₘ h j) := by
          classical
          apply tensorObj_ext
          intro a b hab
          erw [ι_tensorHom_assoc]
          simp only [tensorProjection, ι_tensorObjDesc, ι_tensorObjDesc_assoc]
          by_cases he : a=i ∧ b=j
          · rcases he with ⟨rfl,rfl⟩
            simp only [and_self,dite_true,eqToHom_refl,Category.id_comp,Category.comp_id]
          · simp only [he,dite_false,Limits.zero_comp,Limits.comp_zero]
        change Coalgebra.Antipode.map (i+j) ≫ Coalgebra.comultiplication (i+j) ≫
          tensorProjection Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X i j = _
        have hd := congrFun Coalgebra.Antipode.map_comultiplication (i+j)
        change Coalgebra.Antipode.map (i+j) ≫ Coalgebra.comultiplication (i+j) =
          Coalgebra.comultiplication (i+j) ≫ GradedObject.Monoidal.tensorHom Coalgebra.Antipode.map Coalgebra.Antipode.map (i+j) ≫
            (β_ Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).hom (i+j) at hd
        rw [← Category.assoc, hd]
        simp only [Category.assoc]
        rw [hb]
        erw [eqToHom_naturality_assoc (GradedObject.Monoidal.tensorHom Coalgebra.Antipode.map Coalgebra.Antipode.map) (add_comm i j)]
        erw [eqToHom_naturality_assoc Coalgebra.comultiplication (add_comm i j)]
        rw [← Category.assoc (GradedObject.Monoidal.tensorHom Coalgebra.Antipode.map Coalgebra.Antipode.map (j+i)), hp]
        rfl
      have dt (X : GrVect F2) {i j : ℤ} (h : i=j)
          (φ : Module.Dual F2 (X i)) (x : X j) :
          (show Module.Dual F2 (X j) from
            (eqToHom (congrArg (degreewiseDual X) h)).hom φ) x =
          φ ((eqToHom (congrArg X h.symm)).hom x) := by
        subst j
        rfl
      funext n
      apply tensorObj_ext
      intro i j hij
      subst n
      change ιTensorObj _ _ i j (i+j) rfl ≫ convolutionMultiplication Coalgebra.dualSteenrod (i+j) ≫ conjugation (i+j) =
        ιTensorObj _ _ i j (i+j) rfl ≫ GradedObject.Monoidal.tensorHom conjugation conjugation (i+j) ≫
          (β_ steenrod.X steenrod.X).hom (i+j) ≫ convolutionMultiplication Coalgebra.dualSteenrod (i+j)
      simp only [convolutionMultiplication, ι_tensorObjDesc_assoc,
        eqToHom_refl]
      erw [ι_tensorHom_assoc]
      change _ = (conjugation i ⊗ₘ conjugation j) ≫
        ιTensorObj steenrod.X steenrod.X i j (i+j) rfl ≫
          tensorObjDesc (fun r s h => (β_ (steenrod.X r) (steenrod.X s)).hom ≫ ιTensorObj steenrod.X steenrod.X s r (i+j) _) ≫ _
      simp only [ι_tensorObjDesc_assoc, Category.assoc, ι_tensorObjDesc]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro a
      apply LinearMap.ext
      intro b
      change Module.Dual F2 (Coalgebra.dualSteenrod.X i) at a
      change Module.Dual F2 (Coalgebra.dualSteenrod.X j) at b
      apply LinearMap.ext
      intro x
      change TensorProduct.dualDistrib F2 (Coalgebra.dualSteenrod.X i) (Coalgebra.dualSteenrod.X j)
          (TensorProduct.tmul F2 a b)
          ((Coalgebra.Antipode.map (i+j) ≫ comultiplicationComponent Coalgebra.dualSteenrod i j).hom x) =
        (show Module.Dual F2 (Coalgebra.dualSteenrod.X (i+j)) from
          (eqToHom (congrArg (degreewiseDual Coalgebra.dualSteenrod.X) (add_comm j i))).hom
            ((convolutionPairing Coalgebra.dualSteenrod j i).hom
              (TensorProduct.tmul F2 ((conjugation j).hom b) ((conjugation i).hom a)))) x
      rw [dt Coalgebra.dualSteenrod.X (add_comm j i), hs]
      have heval (z : TensorProduct F2 (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X i)) :
          TensorProduct.dualDistrib F2 (Coalgebra.dualSteenrod.X i) (Coalgebra.dualSteenrod.X j)
            (TensorProduct.tmul F2 a b)
            (((Coalgebra.Antipode.map j ⊗ₘ Coalgebra.Antipode.map i) ≫
              (β_ (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X i)).hom).hom z) =
          TensorProduct.dualDistrib F2 (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X i)
            (TensorProduct.tmul F2 ((conjugation j).hom b) ((conjugation i).hom a)) z := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul u v => exact mul_comm (a ((Coalgebra.Antipode.map i).hom v)) (b ((Coalgebra.Antipode.map j).hom u))
        | add u v hu hv => simp only [map_add, hu, hv]
      change TensorProduct.dualDistrib F2 (Coalgebra.dualSteenrod.X i) (Coalgebra.dualSteenrod.X j)
        (TensorProduct.tmul F2 a b)
        (((Coalgebra.Antipode.map j ⊗ₘ Coalgebra.Antipode.map i) ≫
          (β_ (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X i)).hom).hom
          ((comultiplicationComponent Coalgebra.dualSteenrod j i).hom
            ((eqToHom (congrArg Coalgebra.dualSteenrod.X (add_comm i j))).hom x))) = _
      rw [heval]
      rfl)

theorem conjugation_involutive : conjugation ≫ conjugation = 𝟙 steenrod.X := by
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change Module.Dual KIP126.Core.Algebra.F2 (Coalgebra.Carrier n) at f
  apply LinearMap.ext
  intro x
  change f ((Coalgebra.Antipode.map n).hom ((Coalgebra.Antipode.map n).hom x)) = f x
  exact congrArg f (congrArg (fun h => h.hom x) (congrFun Coalgebra.Antipode.map_involutive n))

theorem dualLeftAction_unit (M : SourceComodule) :
    (η[steenrod.X] ▷ GradedDual.degreewiseDual M.A) ≫ dualLeftAction M =
      (λ_ (GradedDual.degreewiseDual M.A)).hom := by
  exact (open KIP126.Core.Algebra KIP126.Algebra.GradedVectorSpace KIP126.Algebra.GradedDual in by
    set_option backward.isDefEq.respectTransparency false in
      have inclusion_rightUnitor (X : GrVect F2) (n : ℤ) :
        GradedObject.Monoidal.ιTensorObj X (𝟙_ (GrVect F2)) n 0 n (add_zero n) ≫
          (ρ_ X).hom n = (X n ◁ GradedObject.Monoidal.tensorUnit₀.hom) ≫ (ρ_ (X n)).hom := by
        apply (cancel_mono ((ρ_ X).inv n)).1
        simp only [Category.assoc]
        rw [show (ρ_ X).hom n ≫ (ρ_ X).inv n = 𝟙 _ from congrFun (ρ_ X).hom_inv_id n]
        erw [Category.comp_id]
        change _ = (X n ◁ GradedObject.Monoidal.tensorUnit₀.hom) ≫ (ρ_ (X n)).hom ≫
          (ρ_ (X n)).inv ≫ (X n ◁ GradedObject.Monoidal.tensorUnit₀.inv) ≫
            GradedObject.Monoidal.ιTensorObj _ _ _ _ _ _
        simp only [Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc]
        rfl
      have inclusion_rightUnitor_transport (X : GrVect F2) (n m : ℤ) (h : n = m) :
        GradedObject.Monoidal.ιTensorObj X (𝟙_ (GrVect F2)) n 0 m ((add_zero n).trans h) ≫
          (ρ_ X).hom m = (X n ◁ GradedObject.Monoidal.tensorUnit₀.hom) ≫
            (ρ_ (X n)).hom ≫ eqToHom (congrArg X h) := by
        subst m
        simpa only [eqToHom_refl, Category.comp_id] using inclusion_rightUnitor X n
      have contraction (X Y : GrVect F2) (e : Y ⟶ 𝟙_ (GrVect F2)) (n : ℤ) :
        (X ◁ e) (n + 0) ≫ (ρ_ X).hom (n + 0) =
          tensorProjection X Y n 0 ≫
            (X n ◁ (e 0 ≫ GradedObject.Monoidal.tensorUnit₀.hom)) ≫
              (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm) := by
        classical
        apply GradedObject.Monoidal.tensorObj_ext
        intro i j h
        change _ ≫ GradedObject.Monoidal.tensorHom (𝟙 X) e (n + 0) ≫ _ = _
        erw [GradedObject.Monoidal.ι_tensorHom_assoc]
        by_cases hj : j = 0
        · subst j
          have hi : i = n := by simpa using h
          subst i
          simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc_assoc]
          simp only [and_self, dite_true, eqToHom_refl, Category.id_comp]
          erw [inclusion_rightUnitor_transport X n (n + 0) (add_zero n).symm]
          simp only [whiskerLeft_comp, Category.assoc]
          erw [id_tensorHom]
        · have hz : e j = 0 := (GradedObject.Monoidal.isInitialTensorUnitApply j hj).isZero.eq_of_tgt _ _
          simp only [hz, MonoidalPreadditive.tensor_zero, CategoryTheory.Limits.zero_comp]
          simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc_assoc, hj, and_false, dite_false,
            CategoryTheory.Limits.zero_comp]
      have counit_component (n : ℤ) :
        coactionComponent M n 0 ≫ (M.A n ◁ scalarCounit Coalgebra.dualSteenrod) ≫
          (ρ_ (M.A n)).hom ≫ eqToHom (congrArg M.A (add_zero n).symm) = 𝟙 _ := by
        change M.a (n + 0) ≫ tensorProjection M.A Coalgebra.dualSteenrod.X n 0 ≫
          (M.A n ◁ scalarCounit Coalgebra.dualSteenrod) ≫ (ρ_ (M.A n)).hom ≫ _ = _
        erw [← contraction M.A Coalgebra.dualSteenrod.X (ComonObj.counit (X := Coalgebra.dualSteenrod.X)) n]
        rw [← Category.assoc]
        have h := congrFun M.counit (n+0)
        change M.a (n+0) ≫ ((M.A ◁ ComonObj.counit (X := Coalgebra.dualSteenrod.X)) ≫ (ρ_ M.A).hom) (n+0) = 𝟙 _ at h
        change M.a (n+0) ≫ ((M.A ◁ ComonObj.counit (X := Coalgebra.dualSteenrod.X)) (n+0) ≫ (ρ_ M.A).hom (n+0)) = 𝟙 _ at h
        exact h
      have convolution_unit_zero (C : Comon (GrVect F2)) :
        (show ModuleCat.of F2 F2 ⟶ (𝟙_ (GrVect F2)) 0 from
          GradedObject.Monoidal.tensorUnit₀.inv) ≫ convolutionUnit C 0 =
          ModuleCat.ofHom (LinearMap.toSpanSingleton F2 (Module.Dual F2 (C.X 0)) (scalarCounit C).hom) := by
        classical
        simp only [convolutionUnit, dite_true]
        erw [Iso.inv_hom_id_assoc]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        apply LinearMap.ext
        intro x
        simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply]
        erw [LinearMap.dualMap_apply, LinearMap.toSpanSingleton_apply]
      have dual_transport (X : GrVect F2) {i j : ℤ} (h : i = j)
        (φ : Module.Dual F2 (X i)) (x : X j) :
        (show Module.Dual F2 (X j) from ((eqToHom (congrArg (degreewiseDual X) h)).hom φ)) x =
          φ ((eqToHom (congrArg X h.symm)).hom x) := by
        subst j
        rfl
      have dual_counit_eval {M N : ModuleCat F2} (r : N ⟶ ModuleCat.of F2 F2)
        (φ : Module.Dual F2 M) (z : TensorProduct F2 M N) :
        TensorProduct.dualDistrib F2 M N (TensorProduct.tmul F2 φ r.hom) z =
          φ (((M ◁ r) ≫ (ρ_ M).hom).hom z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
            change φ a * r.hom b = φ (r.hom b • a)
            simp only [map_smul, smul_eq_mul, mul_comm]
        | add a b ha hb => simp only [map_add, ha, hb]
      have hχ : (conjugation 0).hom (scalarCounit Coalgebra.dualSteenrod).hom =
          (scalarCounit Coalgebra.dualSteenrod).hom := by
        apply LinearMap.ext
        intro x
        change (GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).hom.hom
          ((Coalgebra.counit 0).hom ((Coalgebra.Antipode.map 0).hom x)) =
          (GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).hom.hom
            ((Coalgebra.counit 0).hom x)
        exact congrArg (GradedObject.Monoidal.tensorUnit₀ (C := ModuleCat F2) (I := ℤ)).hom.hom
          (congrArg (fun f => f.hom x) (congrFun Coalgebra.Antipode.map_counit 0))
      classical
      apply (cancel_epi (λ_ (degreewiseDual M.A)).inv).1
      rw [Iso.inv_hom_id]
      funext n
      change (λ_ (degreewiseDual M.A)).inv n ≫
        GradedObject.Monoidal.tensorHom (convolutionUnit Coalgebra.dualSteenrod) (𝟙 (degreewiseDual M.A)) n ≫
          dualLeftAction M n = 𝟙 _
      change ((λ_ (degreewiseDual M.A n)).inv ≫
        (GradedObject.Monoidal.tensorUnit₀.inv ▷ degreewiseDual M.A n) ≫
          GradedObject.Monoidal.ιTensorObj _ _ 0 n n (zero_add n)) ≫ _ ≫ _ = _
      simp only [Category.assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
        dualLeftAction, GradedObject.Monoidal.ι_tensorObjDesc]
      erw [tensorHom_id, ← comp_whiskerRight_assoc, convolution_unit_zero Coalgebra.dualSteenrod]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change Module.Dual F2 (M.A n) at φ
      apply LinearMap.ext
      intro x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
        ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.toSpanSingleton_apply_one]
      change (show Module.Dual F2 (M.A n) from
        (eqToHom (congrArg (degreewiseDual M.A) (zero_add n))).hom
          ((dualLeftPairing M 0 n).hom (TensorProduct.tmul F2 (scalarCounit Coalgebra.dualSteenrod).hom φ))) x = φ x
      rw [dual_transport M.A (zero_add n)]
      simp only [dualLeftPairing, ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [dual_transport M.A (add_comm n 0)]
      change TensorProduct.dualDistrib F2 (M.A n) (Coalgebra.dualSteenrod.X 0)
        (TensorProduct.tmul F2 φ ((conjugation 0).hom (scalarCounit Coalgebra.dualSteenrod).hom))
          ((coactionComponent M n 0).hom
            ((eqToHom (congrArg M.A (zero_add n).symm) ≫
              eqToHom (congrArg M.A (add_comm n 0).symm)).hom x)) = φ x
      rw [hχ, eqToHom_trans, dual_counit_eval (scalarCounit Coalgebra.dualSteenrod) φ]
      change φ (((coactionComponent M n 0 ≫ (M.A n ◁ scalarCounit Coalgebra.dualSteenrod) ≫
        (ρ_ (M.A n)).hom).hom) ((eqToHom (congrArg M.A (add_zero n).symm)).hom x)) = φ x
      apply congrArg φ
      apply (ModuleCat.mono_iff_injective (eqToHom (congrArg M.A (add_zero n).symm))).mp inferInstance
      exact congrArg (fun f => f.hom ((eqToHom (congrArg M.A (add_zero n).symm)).hom x))
        (counit_component n))

set_option maxHeartbeats 1000000 in
theorem dualLeftAction_assoc (M : SourceComodule) :
    (μ[steenrod.X] ▷ GradedDual.degreewiseDual M.A) ≫ dualLeftAction M =
      (α_ steenrod.X steenrod.X (GradedDual.degreewiseDual M.A)).hom ≫
        (steenrod.X ◁ dualLeftAction M) ≫ dualLeftAction M := by
  exact (open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Algebra.GradedVectorSpace KIP126.Algebra.GradedDual GradedObject.Monoidal in by
    set_option backward.isDefEq.respectTransparency false in
      have assoc_projection (X Y Z : GrVect F2) (i j k : ℤ) :
          (α_ X Y Z).hom ((i+j)+k) ≫
            eqToHom (congrArg (show GrVect F2 from X ⊗ (Y ⊗ Z)) (add_assoc i j k)) ≫
              tensorProjection X (Y ⊗ Z) i (j+k) ≫ (X i ◁ tensorProjection Y Z j k) =
          tensorProjection (X ⊗ Y) Z (i+j) k ≫
            (tensorProjection X Y i j ▷ Z k) ≫ (α_ (X i) (Y j) (Z k)).hom := by
        classical
        have ht (A B : GrVect F2) (a b n m : ℤ) (h : a+b=n) (e : n=m)
            {T : ModuleCat F2} (g : (show GrVect F2 from A ⊗ B) m ⟶ T) :
            ιTensorObj A B a b n h ≫ eqToHom (congrArg (show GrVect F2 from A ⊗ B) e) ≫ g =
              ιTensorObj A B a b m (h.trans e) ≫ g := by
          subst m
          simp only [eqToHom_refl, Category.id_comp]
        apply tensorObj₃'_ext
        intro a b c habc
        erw [ιTensorObj₃'_associator_hom_assoc]
        simp only [ιTensorObj₃, ιTensorObj₃', Category.assoc]
        erw [ht X (Y ⊗ Z) a (b+c) _ _ _ (add_assoc i j k) _]
        simp only [tensorProjection, ι_tensorObjDesc_assoc]
        by_cases ha : a = i
        · subst a
          by_cases hb : b = j
          · subst b
            have hc : c = k := by omega
            subst c
            simp only [and_self, dite_true, eqToHom_refl, Category.id_comp]
            erw [Category.id_comp, ← whiskerLeft_comp, ← comp_whiskerRight_assoc,
              ι_tensorObjDesc, ι_tensorObjDesc]
            simp only [and_self, dite_true, eqToHom_refl, whiskerLeft_id, id_whiskerRight,
              Category.comp_id, Category.id_comp]
          · have hbc : b+c=j+k := by omega
            have hab : ¬(i+b=i+j ∧ c=k) := by omega
            simp only [hab, dite_false, Limits.zero_comp, Limits.comp_zero,
              show i=i ∧ b+c=j+k from ⟨rfl,hbc⟩]
            simp only [and_self, dite_true]
            erw [← whiskerLeft_eqToHom (X i) (congrArg (show GrVect F2 from Y ⊗ Z) hbc)]
            erw [← whiskerLeft_comp, ← whiskerLeft_comp]
            erw [ht Y Z b c _ _ rfl hbc _]
            simp only [ι_tensorObjDesc, hb, false_and, dite_false,
              MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero]
        · simp only [ha, false_and, dite_false, Limits.zero_comp, Limits.comp_zero]
          split_ifs with he
          · rcases he with ⟨hab,rfl⟩
            erw [← eqToHom_whiskerRight (congrArg (show GrVect F2 from X ⊗ Y) hab) (Z c)]
            erw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
            erw [ht X Y a b _ _ rfl hab _]
            simp only [ι_tensorObjDesc, ha, false_and, dite_false,
              MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]
          · simp only [Limits.zero_comp, Limits.comp_zero]

      have projection_naturality (X Y X' Y' : GrVect F2)
          (g : X ⟶ X') (h : Y ⟶ Y') (i j : ℤ) :
          GradedObject.Monoidal.tensorHom g h (i + j) ≫ tensorProjection X' Y' i j =
            tensorProjection X Y i j ≫ (g i ⊗ₘ h j) := by
        classical
        apply tensorObj_ext
        intro a b hab
        erw [ι_tensorHom_assoc]
        simp only [tensorProjection, ι_tensorObjDesc, ι_tensorObjDesc_assoc]
        by_cases he : a = i ∧ b = j
        · rcases he with ⟨rfl, rfl⟩
          simp only [and_self, dite_true, eqToHom_refl, Category.id_comp, Category.comp_id]
        · simp only [he, dite_false, Limits.zero_comp, Limits.comp_zero]
      have degree_transport {X Y : GrVect F2} (f : X ⟶ Y) {n m : ℤ} (h : n = m) :
          f n ≫ eqToHom (congrArg Y h) = eqToHom (congrArg X h) ≫ f m := by
        subst m
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      have component_assoc (M : SourceComodule) (i j k : ℤ) :
          coactionComponent M (i+j) k ≫
            (coactionComponent M i j ▷ Coalgebra.dualSteenrod.X k) ≫
              (α_ (M.A i) (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X k)).hom =
          eqToHom (congrArg M.A (add_assoc i j k)) ≫
            coactionComponent M i (j+k) ≫
              (M.A i ◁ comultiplicationComponent Coalgebra.dualSteenrod j k) := by
        have hc := congrArg (fun f => f ≫ (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).hom ((i+j)+k))
          (congrFun M.coassoc ((i+j)+k))
        change (M.a _ ≫ GradedObject.Monoidal.tensorHom (𝟙 M.A) (ComonObj.comul (X := Coalgebra.dualSteenrod.X)) _ ≫
            (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv _) ≫ (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).hom _ =
          (M.a _ ≫ GradedObject.Monoidal.tensorHom M.a (𝟙 Coalgebra.dualSteenrod.X) _) ≫
            (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).hom _ at hc
        simp only [Category.assoc] at hc
        erw [show (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv ((i+j)+k) ≫
          (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).hom ((i+j)+k) = 𝟙 _ from
            congrFun (α_ M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X).inv_hom_id ((i+j)+k), Category.comp_id] at hc
        dsimp only [coactionComponent, comultiplicationComponent]
        simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
        have hl := projection_naturality M.A Coalgebra.dualSteenrod.X (M.A ⊗ Coalgebra.dualSteenrod.X) Coalgebra.dualSteenrod.X
          M.a (𝟙 Coalgebra.dualSteenrod.X) (i+j) k
        have hr := projection_naturality M.A Coalgebra.dualSteenrod.X M.A (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X)
          (𝟙 M.A) (ComonObj.comul (X := Coalgebra.dualSteenrod.X)) i (j+k)
        erw [tensorHom_id] at hl
        erw [id_tensorHom] at hr
        rw [← reassoc_of% hl, ← reassoc_of% hr]
        rw [← assoc_projection M.A Coalgebra.dualSteenrod.X Coalgebra.dualSteenrod.X i j k]
        simp only [← Category.assoc] at hc ⊢
        rw [← hc]
        simp only [Category.assoc]
        erw [reassoc_of% degree_transport (show M.A ⊗ Coalgebra.dualSteenrod.X ⟶ M.A ⊗ (Coalgebra.dualSteenrod.X ⊗ Coalgebra.dualSteenrod.X) from
          M.A ◁ ComonObj.comul (X := Coalgebra.dualSteenrod.X)) (add_assoc i j k)]
        rw [reassoc_of% degree_transport M.a (add_assoc i j k)]
        rfl

      have dualDistrib_whiskerRight {M N P : ModuleCat F2} (f : M ⟶ N)
          (a : Module.Dual F2 N) (b : Module.Dual F2 P) (z : TensorProduct F2 M P) :
          TensorProduct.dualDistrib F2 M P (TensorProduct.tmul F2 (f.hom.dualMap a) b) z =
            TensorProduct.dualDistrib F2 N P (TensorProduct.tmul F2 a b) ((f ▷ P).hom z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      have dualDistrib_whiskerLeft {M N P : ModuleCat F2} (f : N ⟶ P)
          (a : Module.Dual F2 M) (b : Module.Dual F2 P) (z : TensorProduct F2 M N) :
          TensorProduct.dualDistrib F2 M N (TensorProduct.tmul F2 a (f.hom.dualMap b)) z =
            TensorProduct.dualDistrib F2 M P (TensorProduct.tmul F2 a b) ((M ◁ f).hom z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      have dualDistrib_associator {M N P : ModuleCat F2}
          (a : Module.Dual F2 M) (b : Module.Dual F2 N) (c : Module.Dual F2 P)
          (z : TensorProduct F2 (TensorProduct F2 M N) P) :
          TensorProduct.dualDistrib F2 (TensorProduct F2 M N) P
            (TensorProduct.tmul F2 (TensorProduct.dualDistrib F2 M N (TensorProduct.tmul F2 a b)) c) z =
            TensorProduct.dualDistrib F2 M (TensorProduct F2 N P)
              (TensorProduct.tmul F2 a (TensorProduct.dualDistrib F2 N P (TensorProduct.tmul F2 b c)))
                ((α_ M N P).hom.hom z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
            induction x using TensorProduct.induction_on with
            | zero => simp
            | tmul x w => exact mul_assoc (a x) (b w) (c y)
            | add x w hx hw => simp only [TensorProduct.add_tmul, map_add, hx, hw]
        | add x y hx hy => simp only [map_add, hx, hy]
      have dual_transport (X : GrVect F2) {i j : ℤ} (h : i = j)
          (φ : Module.Dual F2 (X i)) (x : X j) :
          (show Module.Dual F2 (X j) from
            (eqToHom (congrArg (degreewiseDual X) h)).hom φ) x =
            φ ((eqToHom (congrArg X h.symm)).hom x) := by
        subst j
        rfl

      have rightPairAssoc (M : SourceComodule) (i j k : ℤ)
          (φ : Module.Dual F2 (M.A i))
          (a : Module.Dual F2 (Coalgebra.dualSteenrod.X j))
          (b : Module.Dual F2 (Coalgebra.dualSteenrod.X k)) :
          (dualRightPairing M (i+j) k).hom
            (TensorProduct.tmul F2 ((dualRightPairing M i j).hom (TensorProduct.tmul F2 φ a)) b) =
          (eqToHom (congrArg (degreewiseDual M.A) (add_assoc i j k).symm)).hom
            ((dualRightPairing M i (j+k)).hom
              (TensorProduct.tmul F2 φ ((convolutionPairing Coalgebra.dualSteenrod j k).hom (TensorProduct.tmul F2 a b)))) := by
        apply LinearMap.ext
        intro x
        rw [dual_transport M.A (add_assoc i j k).symm]
        change TensorProduct.dualDistrib F2 (M.A (i+j)) (Coalgebra.dualSteenrod.X k)
            (TensorProduct.tmul F2 ((coactionComponent M i j).hom.dualMap
              (TensorProduct.dualDistrib F2 (M.A i) (Coalgebra.dualSteenrod.X j) (TensorProduct.tmul F2 φ a))) b)
            ((coactionComponent M (i+j) k).hom x) =
          TensorProduct.dualDistrib F2 (M.A i) (Coalgebra.dualSteenrod.X (j+k))
            (TensorProduct.tmul F2 φ ((comultiplicationComponent Coalgebra.dualSteenrod j k).hom.dualMap
              (TensorProduct.dualDistrib F2 (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X k) (TensorProduct.tmul F2 a b))))
            ((coactionComponent M i (j+k)).hom
              ((eqToHom (congrArg M.A (add_assoc i j k))).hom x))
        rw [dualDistrib_whiskerRight (coactionComponent M i j),
          dualDistrib_whiskerLeft (comultiplicationComponent Coalgebra.dualSteenrod j k)]
        erw [dualDistrib_associator φ a b]
        apply congrArg (TensorProduct.dualDistrib F2 (M.A i) (TensorProduct F2 (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X k))
          (TensorProduct.tmul F2 φ
            (TensorProduct.dualDistrib F2 (Coalgebra.dualSteenrod.X j) (Coalgebra.dualSteenrod.X k) (TensorProduct.tmul F2 a b))))
        exact congrArg (fun f => f.hom x) (component_assoc M i j k)
      have conjugation_pair (i j : ℤ)
          (a : Module.Dual F2 (Coalgebra.dualSteenrod.X i))
          (b : Module.Dual F2 (Coalgebra.dualSteenrod.X j)) :
          (conjugation (i+j)).hom ((convolutionPairing Coalgebra.dualSteenrod i j).hom (TensorProduct.tmul F2 a b)) =
          (eqToHom (congrArg steenrod.X (add_comm j i))).hom
            ((convolutionPairing Coalgebra.dualSteenrod j i).hom
              (TensorProduct.tmul F2 ((conjugation j).hom b) ((conjugation i).hom a))) := by
        have h := congrArg (fun f => ιTensorObj steenrod.X steenrod.X i j (i+j) rfl ≫ f)
          (congrFun conjugation_mul (i+j))
        change ιTensorObj _ _ i j (i+j) rfl ≫ convolutionMultiplication Coalgebra.dualSteenrod (i+j) ≫ conjugation (i+j) =
          ιTensorObj _ _ i j (i+j) rfl ≫ GradedObject.Monoidal.tensorHom conjugation conjugation (i+j) ≫
            (β_ steenrod.X steenrod.X).hom (i+j) ≫ convolutionMultiplication Coalgebra.dualSteenrod (i+j) at h
        simp only [convolutionMultiplication, ι_tensorObjDesc_assoc, eqToHom_refl] at h
        erw [ι_tensorHom_assoc] at h
        change _ = (conjugation i ⊗ₘ conjugation j) ≫
          ιTensorObj steenrod.X steenrod.X i j (i+j) rfl ≫
            tensorObjDesc (fun r s h => (β_ (steenrod.X r) (steenrod.X s)).hom ≫ ιTensorObj steenrod.X steenrod.X s r (i+j) _) ≫ _ at h
        simp only [ι_tensorObjDesc_assoc, Category.assoc, ι_tensorObjDesc] at h
        exact congrArg (fun f => f.hom (TensorProduct.tmul F2 a b)) h
      have rp_transport (M : SourceComodule) {i i' j j' : ℤ}
          (hi : i=i') (hj : j=j') (φ : Module.Dual F2 (M.A i))
          (a : Module.Dual F2 (Coalgebra.dualSteenrod.X j)) :
          (dualRightPairing M i' j').hom
            (TensorProduct.tmul F2 ((eqToHom (congrArg (degreewiseDual M.A) hi)).hom φ)
              ((eqToHom (congrArg steenrod.X hj)).hom a)) =
          (eqToHom (congrArg (degreewiseDual M.A) (congrArg₂ (· + ·) hi hj))).hom
            ((dualRightPairing M i j).hom (TensorProduct.tmul F2 φ a)) := by
        subst i'
        subst j'
        rfl
      funext n
      apply tensorObj₃'_ext
      intro i j k h
      subst n
      change ιTensorObj₃' _ _ _ i j k _ rfl ≫
        GradedObject.Monoidal.tensorHom (convolutionMultiplication Coalgebra.dualSteenrod) (𝟙 _) _ ≫ _ =
          ιTensorObj₃' _ _ _ i j k _ rfl ≫
            (α_ steenrod.X steenrod.X (degreewiseDual M.A)).hom (i+j+k) ≫
              GradedObject.Monoidal.tensorHom (𝟙 _) (dualLeftAction M) (i+j+k) ≫ dualLeftAction M (i+j+k)
      have ha := ιTensorObj₃'_associator_hom steenrod.X steenrod.X (degreewiseDual M.A) i j k (i+j+k) rfl
      change ιTensorObj₃' _ _ _ i j k _ rfl ≫ (α_ steenrod.X steenrod.X (degreewiseDual M.A)).hom (i+j+k) = _ at ha
      simp only [← Category.assoc]
      rw [ha]
      simp only [ιTensorObj₃', ιTensorObj₃, Category.assoc, ι_tensorHom_assoc,
        convolutionMultiplication, dualLeftAction, ι_tensorObjDesc, eqToHom_refl, Category.comp_id]
      erw [tensorHom_id, id_tensorHom]
      rw [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]
      simp only [ι_tensorObjDesc, eqToHom_refl, Category.comp_id]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_threefold
      intro a b φ
      change Module.Dual F2 (Coalgebra.dualSteenrod.X i) at a
      change Module.Dual F2 (Coalgebra.dualSteenrod.X j) at b
      change Module.Dual F2 (M.A k) at φ
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      erw [ModuleCat.MonoidalCategory.whiskerRight_apply,
        ModuleCat.MonoidalCategory.associator_hom_apply,
        ModuleCat.MonoidalCategory.whiskerLeft_apply]
      change (eqToHom (congrArg (degreewiseDual M.A) (add_comm k (i+j)))).hom
        ((dualRightPairing M k (i+j)).hom (TensorProduct.tmul F2 φ
          ((conjugation (i+j)).hom ((convolutionPairing Coalgebra.dualSteenrod i j).hom (TensorProduct.tmul F2 a b))))) =
        (eqToHom (congrArg (degreewiseDual M.A) (add_assoc i j k).symm)).hom
          ((eqToHom (congrArg (degreewiseDual M.A) (add_comm (j+k) i))).hom
            ((dualRightPairing M (j+k) i).hom (TensorProduct.tmul F2
              ((eqToHom (congrArg (degreewiseDual M.A) (add_comm k j))).hom
                ((dualRightPairing M k j).hom (TensorProduct.tmul F2 φ ((conjugation j).hom b))))
              ((conjugation i).hom a))))
      rw [conjugation_pair]
      have ht1 := rp_transport M (Eq.refl k) (add_comm j i) φ
        ((convolutionPairing Coalgebra.dualSteenrod j i).hom
          (TensorProduct.tmul F2 ((conjugation j).hom b) ((conjugation i).hom a)))
      have ht2 := rp_transport M (add_comm k j) (Eq.refl i)
        ((dualRightPairing M k j).hom (TensorProduct.tmul F2 φ ((conjugation j).hom b))) ((conjugation i).hom a)
      simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply] at ht1 ht2
      rw [ht1, ht2, rightPairAssoc M k j i]
      change ((eqToHom (congrArg (degreewiseDual M.A) (congrArg₂ (· + ·) (Eq.refl k) (add_comm j i))) ≫
        eqToHom (congrArg (degreewiseDual M.A) (add_comm k (i+j)))).hom _) =
        ((eqToHom (congrArg (degreewiseDual M.A) (add_assoc k j i).symm) ≫
          eqToHom (congrArg (degreewiseDual M.A) (congrArg₂ (· + ·) (add_comm k j) (Eq.refl i))) ≫
          eqToHom (congrArg (degreewiseDual M.A) (add_comm (j+k) i)) ≫
          eqToHom (congrArg (degreewiseDual M.A) (add_assoc i j k).symm)).hom _)
      simp only [eqToHom_trans])

/-- A right-comodule map transposes to a left-module map in the opposite direction. -/
theorem dualLeftAction_naturality {M N : SourceComodule} (f : M ⟶ N) :
    (steenrod.X ◁ GradedDual.degreewiseDualMap f.f) ≫ dualLeftAction M =
      dualLeftAction N ≫ GradedDual.degreewiseDualMap f.f := by
  set_option backward.isDefEq.respectTransparency false in
    have dt (X : GradedVectorSpace.GrVect KIP126.Core.Algebra.F2) {i j : ℤ} (h : i = j)
        (φ : Module.Dual KIP126.Core.Algebra.F2 (X i)) (x : X j) :
        (show Module.Dual KIP126.Core.Algebra.F2 (X j) from
          (eqToHom (congrArg (GradedDual.degreewiseDual X) h)).hom φ) x =
          φ ((eqToHom (congrArg X h.symm)).hom x) := by
      subst j
      rfl
    have hp (X Y X' Y' : GradedVectorSpace.GrVect KIP126.Core.Algebra.F2)
        (g : X ⟶ X') (h : Y ⟶ Y') (i j : ℤ) :
        GradedObject.Monoidal.tensorHom g h (i + j) ≫ GradedDual.tensorProjection X' Y' i j =
          GradedDual.tensorProjection X Y i j ≫ (g i ⊗ₘ h j) := by
      classical
      apply GradedObject.Monoidal.tensorObj_ext
      intro a b hab
      erw [GradedObject.Monoidal.ι_tensorHom_assoc]
      simp only [GradedDual.tensorProjection,
        GradedObject.Monoidal.ι_tensorObjDesc, GradedObject.Monoidal.ι_tensorObjDesc_assoc]
      by_cases he : a = i ∧ b = j
      · rcases he with ⟨rfl, rfl⟩
        simp only [and_self, dite_true, eqToHom_refl, Category.id_comp, Category.comp_id]
      · simp only [he, dite_false, Limits.zero_comp, Limits.comp_zero]
    have hc (i j : ℤ) : f.f (i + j) ≫ coactionComponent N i j =
        coactionComponent M i j ≫ (f.f i ⊗ₘ 𝟙 (Coalgebra.dualSteenrod.X j)) := by
      have h := congrFun f.h (i + j)
      change M.a (i + j) ≫ GradedObject.Monoidal.tensorHom f.f (𝟙 _) (i + j) =
        f.f (i + j) ≫ N.a (i + j) at h
      dsimp only [coactionComponent]
      rw [← Category.assoc, ← h, Category.assoc, hp]
      rfl
    funext n
    apply GradedObject.Monoidal.tensorObj_ext
    intro i j hij
    subst n
    change _ ≫ GradedObject.Monoidal.tensorHom (𝟙 steenrod.X)
      (GradedDual.degreewiseDualMap f.f) (i + j) ≫ _ = _
    erw [GradedObject.Monoidal.ι_tensorHom_assoc]
    simp only [dualLeftAction, GradedObject.Monoidal.ι_tensorObjDesc,
      eqToHom_refl, Category.comp_id]
    change (𝟙 (steenrod.X i) ⊗ₘ GradedDual.degreewiseDualMap f.f j) ≫ dualLeftPairing M i j =
      GradedObject.Monoidal.ιTensorObj steenrod.X (GradedDual.degreewiseDual N.A) i j (i + j) rfl ≫
        dualLeftAction N (i + j) ≫ GradedDual.degreewiseDualMap f.f (i + j)
    simp only [dualLeftAction, GradedObject.Monoidal.ι_tensorObjDesc_assoc,
      eqToHom_refl, Category.comp_id]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change Module.Dual KIP126.Core.Algebra.F2 (Coalgebra.Carrier i) at a
    change Module.Dual KIP126.Core.Algebra.F2 (N.A j) at φ
    simp only [dualLeftPairing, dualRightPairing, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, TensorProduct.mk_apply,
      LinearMap.compr₂ₛₗ_apply]
    erw [dt M.A (add_comm j i)]
    change _ = (show Module.Dual KIP126.Core.Algebra.F2 (N.A (i+j)) from
      (eqToHom (congrArg (GradedDual.degreewiseDual N.A) (add_comm j i))).hom
        ((dualRightPairing N j i).hom (TensorProduct.tmul KIP126.Core.Algebra.F2 φ
          ((conjugation i).hom a)))) ((f.f (i+j)).hom x)
    rw [dt N.A (add_comm j i)]
    have heval (ψ : Module.Dual KIP126.Core.Algebra.F2 (Coalgebra.Carrier i))
        (z : TensorProduct KIP126.Core.Algebra.F2 (M.A j) (Coalgebra.Carrier i)) :
        TensorProduct.dualDistrib KIP126.Core.Algebra.F2 (M.A j) (Coalgebra.Carrier i)
          (TensorProduct.tmul _ ((f.f j).hom.dualMap φ) ψ) z =
        TensorProduct.dualDistrib KIP126.Core.Algebra.F2 (N.A j) (Coalgebra.Carrier i)
          (TensorProduct.tmul _ φ ψ) ((f.f j ⊗ₘ 𝟙 (Coalgebra.dualSteenrod.X i)).hom z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m c => rfl
      | add z w hz hw => simp only [map_add, hz, hw]
    have ht {p q : ℤ} (h : p = q) :
        eqToHom (congrArg M.A h) ≫ f.f q = f.f p ≫ eqToHom (congrArg N.A h) := by
      subst q
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change TensorProduct.dualDistrib KIP126.Core.Algebra.F2 (M.A j) (Coalgebra.Carrier i)
        (TensorProduct.tmul _ ((f.f j).hom.dualMap φ) ((conjugation i).hom a))
        ((coactionComponent M j i).hom ((eqToHom (congrArg M.A (add_comm j i).symm)).hom x)) =
      TensorProduct.dualDistrib KIP126.Core.Algebra.F2 (N.A j) (Coalgebra.Carrier i)
        (TensorProduct.tmul _ φ ((conjugation i).hom a))
        ((coactionComponent N j i).hom
          ((eqToHom (congrArg N.A (add_comm j i).symm)).hom ((f.f (i+j)).hom x)))
    rw [heval]
    apply congrArg (TensorProduct.dualDistrib KIP126.Core.Algebra.F2 (N.A j) (Coalgebra.Carrier i)
      (TensorProduct.tmul _ φ ((conjugation i).hom a)))
    have hh := congrArg (fun g => g.hom x) (ht (add_comm j i).symm)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [← hh]
    exact (congrArg (fun g => g.hom ((eqToHom (congrArg M.A (add_comm j i).symm)).hom x))
      (hc j i)).symm

end KIP126.Steenrod.Milnor.Module
