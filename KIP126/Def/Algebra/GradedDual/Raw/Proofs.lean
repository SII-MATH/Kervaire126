import KIP126.Def.Algebra.GradedDual.Raw.Data

/-! Associativity and unit properties of the prescribed convolution maps.
They use the same coalgebra's coassociativity and counitality; no algebra
operations or additional finite-dimensionality assumptions are supplied. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u
variable {K : Type u} [Field K] (C : Comon (GrVect K))

theorem convolutionUnit_mul :
    convolutionUnit C ▷ degreewiseDual C.X ≫ convolutionMultiplication C =
      (λ_ (degreewiseDual C.X)).hom := by
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
    have inclusion_leftUnitor_transport (X : GrVect K) (n m : ℤ) (h : n = m) :
      GradedObject.Monoidal.ιTensorObj (𝟙_ (GrVect K)) X 0 n m ((zero_add n).trans h) ≫
        (λ_ X).hom m = (GradedObject.Monoidal.tensorUnit₀.hom ▷ X n) ≫
          (λ_ (X n)).hom ≫ eqToHom (congrArg X h) := by
      subst m
      simpa only [eqToHom_refl, Category.comp_id] using inclusion_leftUnitor X n
    have contraction (X : GrVect K) (e : X ⟶ 𝟙_ (GrVect K)) (n : ℤ) :
      (e ▷ X) (0 + n) ≫ (λ_ X).hom (0 + n) =
        tensorProjection X X 0 n ≫
          ((e 0 ≫ GradedObject.Monoidal.tensorUnit₀.hom) ▷ X n) ≫
            (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm) := by
      classical
      apply GradedObject.Monoidal.tensorObj_ext
      intro i j h
      change _ ≫ GradedObject.Monoidal.tensorHom e (𝟙 X) (0 + n) ≫ _ = _
      erw [GradedObject.Monoidal.ι_tensorHom_assoc]
      by_cases hi : i = 0
      · subst i
        have hj : j = n := by simpa using h
        subst j
        simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc_assoc]
        simp only [and_self, dite_true, eqToHom_refl, Category.id_comp]
        erw [inclusion_leftUnitor_transport X n (0 + n) (zero_add n).symm]
        simp only [comp_whiskerRight, Category.assoc]
        erw [tensorHom_id]
      · have hz : e i = 0 := (GradedObject.Monoidal.isInitialTensorUnitApply i hi).isZero.eq_of_tgt _ _
        simp only [hz, MonoidalPreadditive.zero_tensor, CategoryTheory.Limits.zero_comp]
        simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc_assoc, hi, false_and, dite_false,
          CategoryTheory.Limits.zero_comp]
    have counit_component (C : Comon (GrVect K)) (n : ℤ) :
      comultiplicationComponent C 0 n ≫ (scalarCounit C ▷ C.X n) ≫
        (λ_ (C.X n)).hom ≫ eqToHom (congrArg C.X (zero_add n).symm) = 𝟙 _ := by
      change (ComonObj.comul (X := C.X)) (0 + n) ≫
        tensorProjection C.X C.X 0 n ≫ (scalarCounit C ▷ C.X n) ≫
          (λ_ (C.X n)).hom ≫ eqToHom (congrArg C.X (zero_add n).symm) = _
      erw [← contraction C.X (ComonObj.counit (X := C.X)) n]
      rw [← Category.assoc]
      have h : (ComonObj.comul (X := C.X)) (0 + n) ≫
          (ComonObj.counit (X := C.X) ▷ C.X) (0 + n) = (λ_ C.X).inv (0 + n) :=
        congrFun (ComonObj.counit_comul C.X) (0 + n)
      rw [h]
      exact congrFun (λ_ C.X).inv_hom_id (0 + n)
    have convolution_unit_zero (C : Comon (GrVect K)) :
      (show ModuleCat.of K K ⟶ (𝟙_ (GrVect K)) 0 from
        GradedObject.Monoidal.tensorUnit₀.inv) ≫ convolutionUnit C 0 =
        ModuleCat.ofHom (LinearMap.toSpanSingleton K (Module.Dual K (C.X 0)) (scalarCounit C).hom) := by
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
    have dual_transport (X : GrVect K) {i j : ℤ} (h : i = j)
      (φ : Module.Dual K (X i)) (x : X j) :
      (show Module.Dual K (X j) from ((eqToHom (congrArg (degreewiseDual X) h)).hom φ)) x =
        φ ((eqToHom (congrArg X h.symm)).hom x) := by
      subst j
      rfl
    have dual_counit_eval {M N : ModuleCat.{u} K} (r : M ⟶ ModuleCat.of K K)
      (φ : Module.Dual K N) (z : TensorProduct K M N) :
      TensorProduct.dualDistrib K M N (TensorProduct.tmul K r.hom φ) z =
        φ (((r ▷ N) ≫ (λ_ N).hom).hom z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          change r.hom a * φ b = φ (r.hom a • b)
          simp only [map_smul, smul_eq_mul]
      | add a b ha hb => simp only [map_add, ha, hb]
    classical
    apply (cancel_epi (λ_ (degreewiseDual C.X)).inv).1
    rw [Iso.inv_hom_id]
    funext n
    change (λ_ (degreewiseDual C.X)).inv n ≫
      GradedObject.Monoidal.tensorHom (convolutionUnit C) (𝟙 (degreewiseDual C.X)) n ≫
        convolutionMultiplication C n = 𝟙 _
    change ((λ_ (degreewiseDual C.X n)).inv ≫
      (GradedObject.Monoidal.tensorUnit₀.inv ▷ degreewiseDual C.X n) ≫
        GradedObject.Monoidal.ιTensorObj _ _ 0 n n (zero_add n)) ≫ _ ≫ _ = _
    simp only [Category.assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      convolutionMultiplication, GradedObject.Monoidal.ι_tensorObjDesc]
    erw [tensorHom_id, ← comp_whiskerRight_assoc, convolution_unit_zero C]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change Module.Dual K (C.X n) at φ
    apply LinearMap.ext
    intro x
    simp only [convolutionPairing, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, LinearMap.toSpanSingleton_apply_one]
    rw [dual_transport C.X (zero_add n)]
    erw [LinearMap.dualMap_apply]
    erw [dual_counit_eval (scalarCounit C) φ]
    change φ (((comultiplicationComponent C 0 n ≫ (scalarCounit C ▷ C.X n) ≫
      (λ_ (C.X n)).hom).hom) ((eqToHom (congrArg C.X (zero_add n).symm)).hom x)) = φ x
    apply congrArg φ
    apply (ModuleCat.mono_iff_injective (eqToHom (congrArg C.X (zero_add n).symm))).mp inferInstance
    exact congrArg (fun f => f.hom ((eqToHom (congrArg C.X (zero_add n).symm)).hom x))
      (counit_component C n)

theorem convolutionMul_unit :
    degreewiseDual C.X ◁ convolutionUnit C ≫ convolutionMultiplication C =
      (ρ_ (degreewiseDual C.X)).hom := by
  set_option backward.isDefEq.respectTransparency false in
    have inclusion_rightUnitor (X : GrVect K) (n : ℤ) :
      GradedObject.Monoidal.ιTensorObj X (𝟙_ (GrVect K)) n 0 n (add_zero n) ≫
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
    have inclusion_rightUnitor_transport (X : GrVect K) (n m : ℤ) (h : n = m) :
      GradedObject.Monoidal.ιTensorObj X (𝟙_ (GrVect K)) n 0 m ((add_zero n).trans h) ≫
        (ρ_ X).hom m = (X n ◁ GradedObject.Monoidal.tensorUnit₀.hom) ≫
          (ρ_ (X n)).hom ≫ eqToHom (congrArg X h) := by
      subst m
      simpa only [eqToHom_refl, Category.comp_id] using inclusion_rightUnitor X n
    have contraction (X : GrVect K) (e : X ⟶ 𝟙_ (GrVect K)) (n : ℤ) :
      (X ◁ e) (n + 0) ≫ (ρ_ X).hom (n + 0) =
        tensorProjection X X n 0 ≫
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
    have counit_component (C : Comon (GrVect K)) (n : ℤ) :
      comultiplicationComponent C n 0 ≫ (C.X n ◁ scalarCounit C) ≫
        (ρ_ (C.X n)).hom ≫ eqToHom (congrArg C.X (add_zero n).symm) = 𝟙 _ := by
      change (ComonObj.comul (X := C.X)) (n + 0) ≫
        tensorProjection C.X C.X n 0 ≫ (C.X n ◁ scalarCounit C) ≫
          (ρ_ (C.X n)).hom ≫ eqToHom (congrArg C.X (add_zero n).symm) = _
      erw [← contraction C.X (ComonObj.counit (X := C.X)) n]
      rw [← Category.assoc]
      have h : (ComonObj.comul (X := C.X)) (n + 0) ≫
          (C.X ◁ ComonObj.counit (X := C.X)) (n + 0) = (ρ_ C.X).inv (n + 0) :=
        congrFun (ComonObj.comul_counit C.X) (n + 0)
      rw [h]
      exact congrFun (ρ_ C.X).inv_hom_id (n + 0)
    have convolution_unit_zero (C : Comon (GrVect K)) :
      (show ModuleCat.of K K ⟶ (𝟙_ (GrVect K)) 0 from
        GradedObject.Monoidal.tensorUnit₀.inv) ≫ convolutionUnit C 0 =
        ModuleCat.ofHom (LinearMap.toSpanSingleton K (Module.Dual K (C.X 0)) (scalarCounit C).hom) := by
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
    have dual_transport (X : GrVect K) {i j : ℤ} (h : i = j)
      (φ : Module.Dual K (X i)) (x : X j) :
      (show Module.Dual K (X j) from ((eqToHom (congrArg (degreewiseDual X) h)).hom φ)) x =
        φ ((eqToHom (congrArg X h.symm)).hom x) := by
      subst j
      rfl
    have dual_counit_eval {M N : ModuleCat.{u} K} (r : N ⟶ ModuleCat.of K K)
      (φ : Module.Dual K M) (z : TensorProduct K M N) :
      TensorProduct.dualDistrib K M N (TensorProduct.tmul K φ r.hom) z =
        φ (((M ◁ r) ≫ (ρ_ M).hom).hom z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          change φ a * r.hom b = φ (r.hom b • a)
          simp only [map_smul, smul_eq_mul, mul_comm]
      | add a b ha hb => simp only [map_add, ha, hb]
    classical
    apply (cancel_epi (ρ_ (degreewiseDual C.X)).inv).1
    rw [Iso.inv_hom_id]
    funext n
    change (ρ_ (degreewiseDual C.X)).inv n ≫
      GradedObject.Monoidal.tensorHom (𝟙 (degreewiseDual C.X)) (convolutionUnit C) n ≫
        convolutionMultiplication C n = 𝟙 _
    change ((ρ_ (degreewiseDual C.X n)).inv ≫
      (degreewiseDual C.X n ◁ GradedObject.Monoidal.tensorUnit₀.inv) ≫
        GradedObject.Monoidal.ιTensorObj _ _ n 0 n (add_zero n)) ≫ _ ≫ _ = _
    simp only [Category.assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      convolutionMultiplication, GradedObject.Monoidal.ι_tensorObjDesc]
    erw [id_tensorHom, ← whiskerLeft_comp_assoc, convolution_unit_zero C]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change Module.Dual K (C.X n) at φ
    apply LinearMap.ext
    intro x
    simp only [convolutionPairing, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    erw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply, LinearMap.toSpanSingleton_apply_one]
    rw [dual_transport C.X (add_zero n)]
    erw [LinearMap.dualMap_apply]
    erw [dual_counit_eval (scalarCounit C) φ]
    change φ (((comultiplicationComponent C n 0 ≫ (C.X n ◁ scalarCounit C) ≫
      (ρ_ (C.X n)).hom).hom) ((eqToHom (congrArg C.X (add_zero n).symm)).hom x)) = φ x
    apply congrArg φ
    apply (ModuleCat.mono_iff_injective (eqToHom (congrArg C.X (add_zero n).symm))).mp inferInstance
    exact congrArg (fun f => f.hom ((eqToHom (congrArg C.X (add_zero n).symm)).hom x))
      (counit_component C n)

set_option maxHeartbeats 1000000 in
theorem convolutionMul_assoc :
    (convolutionMultiplication C ▷ degreewiseDual C.X) ≫ convolutionMultiplication C =
      (α_ (degreewiseDual C.X) (degreewiseDual C.X) (degreewiseDual C.X)).hom ≫
        (degreewiseDual C.X ◁ convolutionMultiplication C) ≫
          convolutionMultiplication C := by
  set_option backward.isDefEq.respectTransparency false in
    have assoc_projection (X Y Z : GrVect K) (i j k : ℤ) :
        (α_ X Y Z).hom ((i+j)+k) ≫
          eqToHom (congrArg (show GrVect K from X ⊗ (Y ⊗ Z)) (add_assoc i j k)) ≫
            tensorProjection X (Y ⊗ Z) i (j+k) ≫ (X i ◁ tensorProjection Y Z j k) =
        tensorProjection (X ⊗ Y) Z (i+j) k ≫
          (tensorProjection X Y i j ▷ Z k) ≫ (α_ (X i) (Y j) (Z k)).hom := by
      classical
      have ht (A B : GrVect K) (a b n m : ℤ) (h : a+b=n) (e : n=m)
          {T : ModuleCat K} (g : (show GrVect K from A ⊗ B) m ⟶ T) :
          GradedObject.Monoidal.ιTensorObj A B a b n h ≫ eqToHom (congrArg (show GrVect K from A ⊗ B) e) ≫ g =
            GradedObject.Monoidal.ιTensorObj A B a b m (h.trans e) ≫ g := by
        subst m
        simp only [eqToHom_refl, Category.id_comp]
      apply GradedObject.Monoidal.tensorObj₃'_ext
      intro a b c habc
      erw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc]
      simp only [GradedObject.Monoidal.ιTensorObj₃, GradedObject.Monoidal.ιTensorObj₃', Category.assoc]
      erw [ht X (Y ⊗ Z) a (b+c) _ _ _ (add_assoc i j k) _]
      simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc_assoc]
      by_cases ha : a = i
      · subst a
        by_cases hb : b = j
        · subst b
          have hc : c = k := by omega
          subst c
          simp only [and_self, dite_true, eqToHom_refl, Category.id_comp]
          erw [Category.id_comp, ← whiskerLeft_comp, ← comp_whiskerRight_assoc,
            GradedObject.Monoidal.ι_tensorObjDesc, GradedObject.Monoidal.ι_tensorObjDesc]
          simp only [and_self, dite_true, eqToHom_refl, whiskerLeft_id, id_whiskerRight,
            Category.comp_id, Category.id_comp]
        · have hbc : b+c=j+k := by omega
          have hab : ¬(i+b=i+j ∧ c=k) := by omega
          simp only [hab, dite_false, Limits.zero_comp, Limits.comp_zero,
            show i=i ∧ b+c=j+k from ⟨rfl,hbc⟩]
          simp only [and_self, dite_true]
          erw [← whiskerLeft_eqToHom (X i) (congrArg (show GrVect K from Y ⊗ Z) hbc)]
          erw [← whiskerLeft_comp, ← whiskerLeft_comp]
          erw [ht Y Z b c _ _ rfl hbc _]
          simp only [GradedObject.Monoidal.ι_tensorObjDesc, hb, false_and, dite_false,
            MonoidalPreadditive.whiskerLeft_zero, Limits.comp_zero]
      · simp only [ha, false_and, dite_false, Limits.zero_comp, Limits.comp_zero]
        split_ifs with he
        · rcases he with ⟨hab,rfl⟩
          erw [← eqToHom_whiskerRight (congrArg (show GrVect K from X ⊗ Y) hab) (Z c)]
          erw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
          erw [ht X Y a b _ _ rfl hab _]
          simp only [GradedObject.Monoidal.ι_tensorObjDesc, ha, false_and, dite_false,
            MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]
        · simp only [Limits.zero_comp, Limits.comp_zero]

    have projection_naturality (X Y X' Y' : GrVect K)
        (g : X ⟶ X') (h : Y ⟶ Y') (i j : ℤ) :
        GradedObject.Monoidal.tensorHom g h (i + j) ≫ tensorProjection X' Y' i j =
          tensorProjection X Y i j ≫ (g i ⊗ₘ h j) := by
      classical
      apply GradedObject.Monoidal.tensorObj_ext
      intro a b hab
      erw [GradedObject.Monoidal.ι_tensorHom_assoc]
      simp only [tensorProjection, GradedObject.Monoidal.ι_tensorObjDesc, GradedObject.Monoidal.ι_tensorObjDesc_assoc]
      by_cases he : a = i ∧ b = j
      · rcases he with ⟨rfl, rfl⟩
        simp only [and_self, dite_true, eqToHom_refl, Category.id_comp, Category.comp_id]
      · simp only [he, dite_false, Limits.zero_comp, Limits.comp_zero]
    have degree_transport {X Y : GrVect K} (f : X ⟶ Y) {n m : ℤ} (h : n = m) :
        f n ≫ eqToHom (congrArg Y h) = eqToHom (congrArg X h) ≫ f m := by
      subst m
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have component_assoc (C : Comon (GrVect K)) (i j k : ℤ) :
        comultiplicationComponent C (i+j) k ≫
          (comultiplicationComponent C i j ▷ C.X k) ≫
            (α_ (C.X i) (C.X j) (C.X k)).hom =
        eqToHom (congrArg C.X (add_assoc i j k)) ≫
          comultiplicationComponent C i (j+k) ≫
            (C.X i ◁ comultiplicationComponent C j k) := by
      have hc := congrFun (ComonObj.comul_assoc C.X).symm ((i+j)+k)
      change (ComonObj.comul (X := C.X)) _ ≫
        GradedObject.Monoidal.tensorHom (ComonObj.comul (X := C.X)) (𝟙 C.X) _ ≫
          (α_ C.X C.X C.X).hom _ =
          (ComonObj.comul (X := C.X)) _ ≫
            GradedObject.Monoidal.tensorHom (𝟙 C.X) (ComonObj.comul (X := C.X)) _ at hc
      dsimp only [comultiplicationComponent]
      simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
      have hl := projection_naturality C.X C.X (C.X ⊗ C.X) C.X
        (ComonObj.comul (X := C.X)) (𝟙 C.X) (i+j) k
      have hr := projection_naturality C.X C.X C.X (C.X ⊗ C.X)
        (𝟙 C.X) (ComonObj.comul (X := C.X)) i (j+k)
      erw [tensorHom_id] at hl
      erw [id_tensorHom] at hr
      rw [← reassoc_of% hl, ← reassoc_of% hr]
      rw [← assoc_projection C.X C.X C.X i j k]
      simp only [← Category.assoc] at hc ⊢
      rw [hc]
      simp only [Category.assoc]
      erw [reassoc_of% degree_transport (show C.X ⊗ C.X ⟶ C.X ⊗ (C.X ⊗ C.X) from
        C.X ◁ ComonObj.comul (X := C.X)) (add_assoc i j k)]
      rw [reassoc_of% degree_transport (ComonObj.comul (X := C.X)) (add_assoc i j k)]
      rfl

    have dualDistrib_whiskerRight {M N P : ModuleCat.{u} K} (f : M ⟶ N)
        (a : Module.Dual K N) (b : Module.Dual K P) (z : TensorProduct K M P) :
        TensorProduct.dualDistrib K M P (TensorProduct.tmul K (f.hom.dualMap a) b) z =
          TensorProduct.dualDistrib K N P (TensorProduct.tmul K a b) ((f ▷ P).hom z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    have dualDistrib_whiskerLeft {M N P : ModuleCat.{u} K} (f : N ⟶ P)
        (a : Module.Dual K M) (b : Module.Dual K P) (z : TensorProduct K M N) :
        TensorProduct.dualDistrib K M N (TensorProduct.tmul K a (f.hom.dualMap b)) z =
          TensorProduct.dualDistrib K M P (TensorProduct.tmul K a b) ((M ◁ f).hom z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    have dualDistrib_associator {M N P : ModuleCat.{u} K}
        (a : Module.Dual K M) (b : Module.Dual K N) (c : Module.Dual K P)
        (z : TensorProduct K (TensorProduct K M N) P) :
        TensorProduct.dualDistrib K (TensorProduct K M N) P
          (TensorProduct.tmul K (TensorProduct.dualDistrib K M N (TensorProduct.tmul K a b)) c) z =
          TensorProduct.dualDistrib K M (TensorProduct K N P)
            (TensorProduct.tmul K a (TensorProduct.dualDistrib K N P (TensorProduct.tmul K b c)))
              ((α_ M N P).hom.hom z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul x w => exact mul_assoc (a x) (b w) (c y)
          | add x w hx hw => simp only [TensorProduct.add_tmul, map_add, hx, hw]
      | add x y hx hy => simp only [map_add, hx, hy]
    have dual_transport (X : GrVect K) {i j : ℤ} (h : i = j)
        (φ : Module.Dual K (X i)) (x : X j) :
        (show Module.Dual K (X j) from
          (eqToHom (congrArg (degreewiseDual X) h)).hom φ) x =
          φ ((eqToHom (congrArg X h.symm)).hom x) := by
      subst j
      rfl
    funext n
    apply GradedObject.Monoidal.tensorObj₃'_ext
    intro i j k h
    subst n
    change GradedObject.Monoidal.ιTensorObj₃' _ _ _ i j k _ rfl ≫
      GradedObject.Monoidal.tensorHom (convolutionMultiplication C) (𝟙 _) _ ≫ _ =
        GradedObject.Monoidal.ιTensorObj₃' _ _ _ i j k _ rfl ≫
          (α_ (degreewiseDual C.X) (degreewiseDual C.X) (degreewiseDual C.X)).hom (i + j + k) ≫
            GradedObject.Monoidal.tensorHom (𝟙 _) (convolutionMultiplication C) (i + j + k) ≫
              convolutionMultiplication C (i + j + k)
    have ha := GradedObject.Monoidal.ιTensorObj₃'_associator_hom
      (degreewiseDual C.X) (degreewiseDual C.X) (degreewiseDual C.X) i j k (i + j + k) rfl
    change GradedObject.Monoidal.ιTensorObj₃' _ _ _ i j k _ rfl ≫
        (α_ (degreewiseDual C.X) (degreewiseDual C.X) (degreewiseDual C.X)).hom (i + j + k) = _ at ha
    simp only [← Category.assoc]
    rw [ha]
    simp only [GradedObject.Monoidal.ιTensorObj₃', GradedObject.Monoidal.ιTensorObj₃,
      Category.assoc, GradedObject.Monoidal.ι_tensorHom_assoc,
      convolutionMultiplication,
      GradedObject.Monoidal.ι_tensorObjDesc, eqToHom_refl, Category.comp_id]
    erw [tensorHom_id, id_tensorHom]
    rw [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]
    simp only [GradedObject.Monoidal.ι_tensorObjDesc, eqToHom_refl, Category.comp_id]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro a b c
    change Module.Dual K (C.X i) at a
    change Module.Dual K (C.X j) at b
    change Module.Dual K (C.X k) at c
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply]
    rw [dual_transport C.X (add_assoc i j k).symm]
    change TensorProduct.dualDistrib K (C.X (i+j)) (C.X k)
        (TensorProduct.tmul K ((comultiplicationComponent C i j).hom.dualMap
          (TensorProduct.dualDistrib K (C.X i) (C.X j) (TensorProduct.tmul K a b))) c)
        ((comultiplicationComponent C (i+j) k).hom x) =
      TensorProduct.dualDistrib K (C.X i) (C.X (j+k))
        (TensorProduct.tmul K a ((comultiplicationComponent C j k).hom.dualMap
          (TensorProduct.dualDistrib K (C.X j) (C.X k) (TensorProduct.tmul K b c))))
        ((comultiplicationComponent C i (j+k)).hom
          ((eqToHom (congrArg C.X (add_assoc i j k))).hom x))
    rw [dualDistrib_whiskerRight (comultiplicationComponent C i j),
      dualDistrib_whiskerLeft (comultiplicationComponent C j k)]
    erw [dualDistrib_associator a b c]
    apply congrArg (TensorProduct.dualDistrib K (C.X i) (TensorProduct K (C.X j) (C.X k))
      (TensorProduct.tmul K a
        (TensorProduct.dualDistrib K (C.X j) (C.X k) (TensorProduct.tmul K b c))))
    exact congrArg (fun f => f.hom x) (component_assoc C i j k)

end KIP126.Algebra.GradedDual
