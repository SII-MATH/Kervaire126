module

public import KIP126.Def.Steenrod.MilnorModule.Comparison.Multiplication.Predicates
public import Mathlib.CategoryTheory.Shift.ShiftedHomOpposite
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

@[expose] public section

/-!
# Yoneda and unit laws for the prescribed dual-cobar comparison

The premise is the existing formula on every actual resolution cocycle.
Multiplicativity is a conclusion about derived composition, not an additional
assumption on the comparison.  Proofs require compatibility of the actual
dual resolution with shifts and composition and remain staged separately.
-/

namespace KIP126.Steenrod.Milnor.Module

open KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite
  HomologicalComplex KIP126.Algebra KIP126.Algebra.GradedVectorSpace
  CategoryTheory.MonoidalCategory KIP126.Algebra.GradedDual
  CategoryTheory.GradedObject.Monoidal CochainComplex.HomComplex in
open scoped TensorProduct in
set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual same-degree dual commutes with internal shift.  Over `F2`,
all isomorphisms with a fixed trivial coefficient module as target agree. -/
private theorem dualShift_exists_unique :
    (∀ t : ℤ, Nonempty
      ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).op ⋙ dualToLeftModule ≅
        dualToLeftModule ⋙ GradedModule.internalShift F2 steenrod t)) ∧
    (∀ (t : ℤ) {M : LeftModule} (e f : M ≅ trivialAt t), e = f) := by
  classical
  have r_lineTensorInclusion_isIso (X : GrVect F2) (t j : ℤ) :
      IsIso (ιTensorObj (GradedComodule.degreeLine F2 t) X t j (t+j) rfl) := by
    classical
    let L := GradedComodule.degreeLine F2 t
    let f := ιTensorObj L X t j (t+j) rfl
    let g : (L ⊗ X) (t+j) ⟶ L t ⊗ X j := tensorObjDesc fun a b hab =>
      if ha : a=t then eqToHom (congrArg₂ (fun a b => L a ⊗ X b) ha (by omega : b=j)) else 0
    have hfg : f ≫ g = 𝟙 _ := by
      dsimp [f,g]
      rw [ι_tensorObjDesc]
      simp
    have hgf : g ≫ f = 𝟙 _ := by
      apply tensorObj_ext
      intro a b hab
      by_cases ha : a=t
      · subst a
        have hb : b=j := by omega
        subst b
        dsimp [g]
        rw [ι_tensorObjDesc_assoc]
        simp only [eqToHom_refl]
        exact (Category.comp_id _).symm
      · exact ((GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) a ha).isInitialObj
          (tensorRight (X b))).hom_ext _ _
    exact ⟨⟨g,hfg,hgf⟩⟩

  let r_lineInclusion (X : GrVect F2) (t j n : ℤ) (h : t+j=n) :
      X j ⟶ (GradedComodule.degreeLine F2 t ⊗ X) n :=
    (TensorProduct.lid F2 (X j)).toModuleIso.inv ≫
      ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv ▷ X j) ≫
        ιTensorObj (GradedComodule.degreeLine F2 t) X t j n h

  have r_lineInclusion_isIso (X : GrVect F2) (t j n : ℤ) (h : t+j=n) :
      IsIso (r_lineInclusion X t j n h) := by
    subst n
    letI := r_lineTensorInclusion_isIso X t j
    unfold r_lineInclusion
    infer_instance

  have r_lineInclusion_naturality {X Y : GrVect F2} (f : X ⟶ Y)
      (t j n : ℤ) (h : t+j=n) :
      r_lineInclusion X t j n h ≫ (GradedComodule.degreeLine F2 t ◁ f) n =
        f j ≫ r_lineInclusion Y t j n h := by
    dsimp [r_lineInclusion]
    change _ ≫ _ ≫ ιTensorObj _ _ _ _ _ _ ≫
      GradedObject.Monoidal.tensorHom (𝟙 _) f n = _
    rw [ι_tensorHom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (ιTensorObj (GradedComodule.degreeLine F2 t) Y t j n h).hom
      ((TensorProduct.map _ _) (_ ⊗ₜ[F2] x)) =
        (ιTensorObj (GradedComodule.degreeLine F2 t) Y t j n h).hom (_ ⊗ₜ[F2] (f j).hom x)
    simp


  have r_tensorLineInclusion_isIso (X : GrVect F2) (t j : ℤ) :
      IsIso (ιTensorObj X (GradedComodule.degreeLine F2 t) j t (j+t) rfl) := by
    classical
    let L := GradedComodule.degreeLine F2 t
    let f := ιTensorObj X L j t (j+t) rfl
    let g : (X ⊗ L) (j+t) ⟶ X j ⊗ L t := tensorObjDesc fun a b hab =>
      if hb : b=t then eqToHom (congrArg₂ (fun a b => X a ⊗ L b) (by omega : a=j) hb) else 0
    have hfg : f ≫ g = 𝟙 _ := by
      dsimp [f,g]
      rw [ι_tensorObjDesc]
      simp
    have hgf : g ≫ f = 𝟙 _ := by
      apply tensorObj_ext
      intro a b hab
      by_cases hb : b=t
      · subst b
        have ha : a=j := by omega
        subst a
        dsimp [g]
        rw [ι_tensorObjDesc_assoc]
        simp only [eqToHom_refl]
        exact (Category.comp_id _).symm
      · exact ((GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) b hb).isInitialObj
          (tensorLeft (X a))).hom_ext _ _
    exact ⟨⟨g,hfg,hgf⟩⟩

  let r_rightLineInclusion (X : GrVect F2) (t j n : ℤ) (h : j+t=n) :
      X j ⟶ (X ⊗ GradedComodule.degreeLine F2 t) n :=
    (TensorProduct.rid F2 (X j)).toModuleIso.inv ≫
      (X j ◁ (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv) ≫
        ιTensorObj X (GradedComodule.degreeLine F2 t) j t n h

  have r_rightLineInclusion_isIso (X : GrVect F2) (t j n : ℤ) (h : j+t=n) :
      IsIso (r_rightLineInclusion X t j n h) := by
    subst n
    letI := r_tensorLineInclusion_isIso X t j
    unfold r_rightLineInclusion
    infer_instance

  have r_rightLineInclusion_naturality {X Y : GrVect F2} (f : X ⟶ Y)
      (t j n : ℤ) (h : j+t=n) :
      r_rightLineInclusion X t j n h ≫ (f ▷ GradedComodule.degreeLine F2 t) n =
        f j ≫ r_rightLineInclusion Y t j n h := by
    dsimp [r_rightLineInclusion]
    change _ ≫ _ ≫ ιTensorObj _ _ _ _ _ _ ≫
      GradedObject.Monoidal.tensorHom f (𝟙 _) n = _
    rw [ι_tensorHom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (ιTensorObj Y (GradedComodule.degreeLine F2 t) j t n h).hom
      ((TensorProduct.map _ _) (x ⊗ₜ[F2] _)) =
        (ιTensorObj Y (GradedComodule.degreeLine F2 t) j t n h).hom ((f j).hom x ⊗ₜ[F2] _)
    simp

  let r_shiftDualGradedIso (X : GrVect F2) (t : ℤ) :
      degreewiseDual (GradedComodule.degreeLine F2 t ⊗ X) ≅
        degreewiseDual X ⊗ GradedComodule.degreeLine F2 t := by
    let e (n : ℤ) : degreewiseDual (GradedComodule.degreeLine F2 t ⊗ X) n ≅
        (degreewiseDual X ⊗ GradedComodule.degreeLine F2 t) n := by
      have hl : t+(n-t)=n := by omega
      have hr : (n-t)+t=n := by omega
      letI := r_lineInclusion_isIso X t (n-t) n hl
      letI := r_rightLineInclusion_isIso (degreewiseDual X) t (n-t) n hr
      exact (asIso (r_lineInclusion X t (n-t) n hl)).toLinearEquiv.dualMap.toModuleIso ≪≫
        asIso (r_rightLineInclusion (degreewiseDual X) t (n-t) n hr)
    exact ⟨fun n => (e n).hom, fun n => (e n).inv,
      funext (fun n => (e n).hom_inv_id), funext (fun n => (e n).inv_hom_id)⟩

  have r_shiftDualGradedIso_hom (X : GrVect F2) (t j n : ℤ) (h : j+t=n) :
      (r_shiftDualGradedIso X t).hom n =
        ModuleCat.ofHom (r_lineInclusion X t j n (by omega)).hom.dualMap ≫
          r_rightLineInclusion (degreewiseDual X) t j n h := by
    have hsub : n-t=j := by omega
    subst j
    rfl

  have r_shiftDualGradedIso_naturality {X Y : GrVect F2} (f : X ⟶ Y) (t : ℤ) :
      degreewiseDualMap (GradedComodule.degreeLine F2 t ◁ f) ≫ (r_shiftDualGradedIso X t).hom =
        (r_shiftDualGradedIso Y t).hom ≫ (degreewiseDualMap f ▷ GradedComodule.degreeLine F2 t) := by
    funext n
    change degreewiseDualMap _ n ≫ (r_shiftDualGradedIso X t).hom n =
      (r_shiftDualGradedIso Y t).hom n ≫ _
    rw [r_shiftDualGradedIso_hom X t (n-t) n (by omega),
      r_shiftDualGradedIso_hom Y t (n-t) n (by omega)]
    rw [Category.assoc, r_rightLineInclusion_naturality (degreewiseDualMap f) t (n-t) n (by omega)]
    have hdual :
        degreewiseDualMap (GradedComodule.degreeLine F2 t ◁ f) n ≫
          ModuleCat.ofHom (r_lineInclusion X t (n-t) n (by omega)).hom.dualMap =
        ModuleCat.ofHom (r_lineInclusion Y t (n-t) n (by omega)).hom.dualMap ≫
          degreewiseDualMap f (n-t) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change Module.Dual F2 ((GradedComodule.degreeLine F2 t ⊗ Y) n) at φ
      apply LinearMap.ext
      intro x
      change φ (((r_lineInclusion X t (n-t) n (by omega) ≫
        (GradedComodule.degreeLine F2 t ◁ f) n).hom) x) =
        φ (((f (n-t) ≫ r_lineInclusion Y t (n-t) n (by omega)).hom) x)
      rw [r_lineInclusion_naturality]
    calc
      _ = (degreewiseDualMap (GradedComodule.degreeLine F2 t ◁ f) n ≫
          ModuleCat.ofHom (r_lineInclusion X t (n-t) n (by omega)).hom.dualMap) ≫
          r_rightLineInclusion (degreewiseDual X) t (n-t) n (by omega) :=
        (Category.assoc _ _ _).symm
      _ = (ModuleCat.ofHom (r_lineInclusion Y t (n-t) n (by omega)).hom.dualMap ≫
          degreewiseDualMap f (n-t)) ≫
          r_rightLineInclusion (degreewiseDual X) t (n-t) n (by omega) :=
        congrArg (fun k => k ≫ r_rightLineInclusion (degreewiseDual X) t (n-t) n (by omega)) hdual
      _ = _ := Category.assoc _ _ _



  let r_scalarInsert (t : ℤ) (X : ModuleCat F2) : X ⟶ GradedComodule.degreeLine F2 t t ⊗ X :=
    (TensorProduct.lid F2 X).toModuleIso.inv ≫
      ((GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv ▷ X)

  have r_scalarInsert_naturality (t : ℤ) {X Y : ModuleCat F2} (f : X ⟶ Y) :
      f ≫ r_scalarInsert t Y = r_scalarInsert t X ≫ (GradedComodule.degreeLine F2 t t ◁ f) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change _ ⊗ₜ[F2] f.hom x = (TensorProduct.map _ f.hom) (_ ⊗ₜ[F2] x)
    simp only [TensorProduct.map_tmul]
    rfl

  have r_lineInclusion_tensorProjection (X Y : GrVect F2) (t j i : ℤ) :
      r_lineInclusion (X ⊗ Y) t (j+i) ((t+j)+i) (by omega) ≫
        (α_ (GradedComodule.degreeLine F2 t) X Y).inv ((t+j)+i) ≫
          tensorProjection (GradedComodule.degreeLine F2 t ⊗ X) Y (t+j) i =
      tensorProjection X Y j i ≫ (r_lineInclusion X t j (t+j) rfl ▷ Y i) := by
    classical
    apply tensorObj_ext
    intro a b hab
    change ιTensorObj X Y a b (j+i) hab ≫ r_scalarInsert t _ ≫
      ιTensorObj (GradedComodule.degreeLine F2 t) (X ⊗ Y) t (j+i) ((t+j)+i) _ ≫
        (α_ (GradedComodule.degreeLine F2 t) X Y).inv ((t+j)+i) ≫
          tensorProjection _ _ _ _ = _
    rw [← Category.assoc, r_scalarInsert_naturality]
    simp only [Category.assoc]
    erw [← ιTensorObj₃_eq_assoc (GradedComodule.degreeLine F2 t) X Y t a b ((t+j)+i) (by omega) (j+i) hab]
    erw [ιTensorObj₃_associator_inv_assoc]
    simp only [ιTensorObj₃', Category.assoc, tensorProjection, ι_tensorObjDesc_assoc]
    erw [ι_tensorObjDesc]
    by_cases ha : a=j
    · subst a
      have hb : b=i := by omega
      subst b
      simp only [and_self, dite_true, eqToHom_refl, Category.id_comp]
      change r_scalarInsert t (X j ⊗ Y i) ≫ (α_ _ _ _).inv ≫
        (ιTensorObj _ _ _ _ _ _ ▷ Y i) = _
      change _ = (r_scalarInsert t (X j) ≫ ιTensorObj (GradedComodule.degreeLine F2 t) X t j (t+j) rfl) ▷ Y i
      rw [comp_whiskerRight, ← Category.assoc]
      congr 1
    · have hne : ¬(t+a=t+j ∧ b=i) := by omega
      simp only [hne, ha, false_and, dite_false, Limits.zero_comp, Limits.comp_zero]


  have r_lineInclusion_coactionComponent (M : SourceComodule) (t j i : ℤ) :
      r_lineInclusion M.A t (j+i) ((t+j)+i) (by omega) ≫
        coactionComponent ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) (t+j) i =
      coactionComponent M j i ≫ (r_lineInclusion M.A t j (t+j) rfl ▷ Coalgebra.dualSteenrod.X i) := by
    change r_lineInclusion M.A t (j+i) ((t+j)+i) _ ≫
      (GradedComodule.degreeLine F2 t ◁ M.a) ((t+j)+i) ≫
        (α_ (GradedComodule.degreeLine F2 t) M.A Coalgebra.dualSteenrod.X).inv ((t+j)+i) ≫
          tensorProjection (GradedComodule.degreeLine F2 t ⊗ M.A) Coalgebra.dualSteenrod.X (t+j) i = _
    rw [← Category.assoc, r_lineInclusion_naturality]
    simp only [Category.assoc]
    erw [r_lineInclusion_tensorProjection M.A Coalgebra.dualSteenrod.X t j i]
    rfl


  have r_lineInclusion_cast (X : GrVect F2) (t j j' n n' : ℤ)
      (hj : j=j') (hn : n=n') (h : t+j=n) (h' : t+j'=n') :
      r_lineInclusion X t j n h ≫ eqToHom (congrArg (show GrVect F2 from GradedComodule.degreeLine F2 t ⊗ X) hn) =
        eqToHom (congrArg X hj) ≫ r_lineInclusion X t j' n' h' := by
    subst j'
    subst n'
    simp

  have r_dual_transport (X : GrVect F2) {i j : ℤ} (h : i=j)
      (φ : Module.Dual F2 (X i)) (x : X j) :
      (show Module.Dual F2 (X j) from ((eqToHom (congrArg (degreewiseDual X) h)).hom φ)) x =
        φ ((eqToHom (congrArg X h.symm)).hom x) := by
    subst j
    rfl

  have r_dualLeftPairing_shift (M : SourceComodule) (t i j : ℤ) :
      dualLeftPairing ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) i (t+j) ≫
        ModuleCat.ofHom (r_lineInclusion M.A t (i+j) (i+(t+j)) (by omega)).hom.dualMap =
      (steenrod.X i ◁ ModuleCat.ofHom (r_lineInclusion M.A t j (t+j) rfl).hom.dualMap) ≫
        dualLeftPairing M i j := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro φ
    change Module.Dual F2 ((GradedComodule.degreeLine F2 t ⊗ M.A) (t+j)) at φ
    apply LinearMap.ext
    intro x
    change (show Module.Dual F2 ((GradedComodule.degreeLine F2 t ⊗ M.A) (i+(t+j))) from
      (dualLeftPairing ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) i (t+j)).hom
        (a ⊗ₜ[F2] φ)) ((r_lineInclusion M.A t (i+j) (i+(t+j)) (by omega)).hom x) =
      (show Module.Dual F2 (M.A (i+j)) from (dualLeftPairing M i j).hom
        (a ⊗ₜ[F2] (φ.comp (r_lineInclusion M.A t j (t+j) rfl).hom))) x
    simp only [dualLeftPairing, ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [r_dual_transport ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M).A (add_comm (t+j) i),
      r_dual_transport M.A (add_comm j i)]
    change TensorProduct.dualDistrib F2 _ _ (φ ⊗ₜ[F2] (conjugation i).hom a)
      ((r_lineInclusion M.A t (i+j) (i+(t+j)) (by omega) ≫
        eqToHom (congrArg (show GrVect F2 from GradedComodule.degreeLine F2 t ⊗ M.A) (add_comm i (t+j))) ≫
          coactionComponent ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) (t+j) i).hom x) = _
    rw [← Category.assoc, r_lineInclusion_cast M.A t (i+j) (j+i) (i+(t+j)) ((t+j)+i)
      (add_comm i j) (add_comm i (t+j)) (by omega) (by omega)]
    simp only [Category.assoc]
    rw [r_lineInclusion_coactionComponent]
    change TensorProduct.dualDistrib F2 _ _ (φ ⊗ₜ[F2] (conjugation i).hom a)
      ((r_lineInclusion M.A t j (t+j) rfl ▷ Coalgebra.dualSteenrod.X i).hom
        ((coactionComponent M j i).hom ((eqToHom (congrArg M.A (add_comm i j))).hom x))) =
      TensorProduct.dualDistrib F2 _ _
        ((φ.comp (r_lineInclusion M.A t j (t+j) rfl).hom) ⊗ₜ[F2] (conjugation i).hom a)
          ((coactionComponent M j i).hom ((eqToHom (congrArg M.A (add_comm i j))).hom x))
    generalize (coactionComponent M j i).hom ((eqToHom (congrArg M.A (add_comm i j))).hom x) = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rfl
    | add z w hz hw => simp only [map_add, hz, hw]


  have r_rightLineInclusion_action (A X : GrVect F2) (f : A ⊗ X ⟶ X) (t i j : ℤ) :
      (A i ◁ r_rightLineInclusion X t j (t+j) (add_comm j t)) ≫
        ιTensorObj A (X ⊗ GradedComodule.degreeLine F2 t) i (t+j) (i+(t+j)) rfl ≫
          (α_ A X (GradedComodule.degreeLine F2 t)).inv (i+(t+j)) ≫
            (f ▷ GradedComodule.degreeLine F2 t) (i+(t+j)) =
      ιTensorObj A X i j (i+j) rfl ≫ f (i+j) ≫
        r_rightLineInclusion X t (i+j) (i+(t+j)) (by omega) := by
    let L := GradedComodule.degreeLine F2 t
    let g : X j ⟶ X j ⊗ L t :=
      (TensorProduct.rid F2 (X j)).toModuleIso.inv ≫
        (X j ◁ (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv)
    change (A i ◁ (g ≫ ιTensorObj X L j t (t+j) (add_comm j t))) ≫ _ = _
    rw [whiskerLeft_comp, Category.assoc]
    erw [← ιTensorObj₃_eq_assoc A X L i j t (i+(t+j)) (by omega) (t+j) (add_comm j t)]
    erw [ιTensorObj₃_associator_inv_assoc]
    simp only [ιTensorObj₃', Category.assoc]
    change (A i ◁ g) ≫ (α_ (A i) (X j) (L t)).inv ≫
      (ιTensorObj A X i j (i+j) rfl ▷ L t) ≫
        ιTensorObj (A ⊗ X) L (i+j) t (i+(t+j)) _ ≫
          GradedObject.Monoidal.tensorHom f (𝟙 L) (i+(t+j)) = _
    rw [ι_tensorHom]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro x
    change (ιTensorObj X L (i+j) t (i+(t+j)) _).hom
      ((f (i+j)).hom ((ιTensorObj A X i j (i+j) rfl).hom (a ⊗ₜ[F2] x)) ⊗ₜ[F2] _) = _
    rfl


  have r_shiftDualGradedIso_action (M : SourceComodule) (t : ℤ) :
      dualLeftAction ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) ≫
          (r_shiftDualGradedIso M.A t).hom =
      (steenrod.X ◁ (r_shiftDualGradedIso M.A t).hom) ≫
        GradedModule.internalShiftAction F2 steenrod t (dualLeftModule M) := by
    funext n
    apply tensorObj_ext
    intro i q hiq
    cases hiq
    obtain ⟨j,rfl⟩ : ∃j, q=t+j := ⟨q-t, by omega⟩
    change ιTensorObj steenrod.X (degreewiseDual (GradedComodule.degreeLine F2 t ⊗ M.A)) i (t+j) (i+(t+j)) rfl ≫
      dualLeftAction ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) (i+(t+j)) ≫ (r_shiftDualGradedIso M.A t).hom (i+(t+j)) =
      ιTensorObj steenrod.X (degreewiseDual (GradedComodule.degreeLine F2 t ⊗ M.A)) i (t+j) (i+(t+j)) rfl ≫
        GradedObject.Monoidal.tensorHom (𝟙 steenrod.X) (r_shiftDualGradedIso M.A t).hom (i+(t+j)) ≫ _
    simp only [dualLeftAction, ι_tensorObjDesc_assoc, eqToHom_refl, Category.comp_id]
    erw [ι_tensorHom_assoc, id_tensorHom]
    rw [r_shiftDualGradedIso_hom M.A t (i+j) (i+(t+j)) (by omega),
      r_shiftDualGradedIso_hom M.A t j (t+j) (add_comm j t)]
    rw [← Category.assoc, r_dualLeftPairing_shift]
    simp only [Category.assoc, whiskerLeft_comp]
    change _ = (steenrod.X i ◁ ModuleCat.ofHom (r_lineInclusion M.A t j (t+j) rfl).hom.dualMap) ≫
      (steenrod.X i ◁ r_rightLineInclusion (degreewiseDual M.A) t j (t+j) (add_comm j t)) ≫
        ιTensorObj steenrod.X (degreewiseDual M.A ⊗ GradedComodule.degreeLine F2 t) i (t+j) (i+(t+j)) rfl ≫
          (α_ steenrod.X (degreewiseDual M.A) (GradedComodule.degreeLine F2 t)).inv (i+(t+j)) ≫
            (dualLeftAction M ▷ GradedComodule.degreeLine F2 t) (i+(t+j))
    rw [r_rightLineInclusion_action]
    simp only [dualLeftAction, ι_tensorObjDesc_assoc, eqToHom_refl, Category.comp_id]

  let r_shiftDualModuleIso (M : SourceComodule) (t : ℤ) :
      dualLeftModule ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) ≅
        (GradedModule.internalShift F2 steenrod t).obj (dualLeftModule M) :=
    Monad.Algebra.isoMk (r_shiftDualGradedIso M.A t) (r_shiftDualGradedIso_action M t).symm

  let r_shiftDualNatIso (t : ℤ) :
      (GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).op ⋙ dualToLeftModule ≅
        dualToLeftModule ⋙ GradedModule.internalShift F2 steenrod t :=
    NatIso.ofComponents (fun M => r_shiftDualModuleIso M.unop t) (fun f => by
      apply Monad.Algebra.Hom.ext
      exact r_shiftDualGradedIso_naturality f.unop.f t)


  have r_lineEndIso_hom (t : ℤ) (e : GradedComodule.degreeLine F2 t ≅ GradedComodule.degreeLine F2 t) :
      e.hom = 𝟙 _ := by
    classical
    let L := GradedComodule.degreeLine F2 t
    let E : L t ≅ ModuleCat.of F2 F2 := GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)
    have hj (f g : L ⟶ L) (h : E.inv ≫ f t ≫ E.hom = E.inv ≫ g t ≫ E.hom) : f=g := by
      funext n
      by_cases hn : n=t
      · subst n
        exact (cancel_epi E.inv).mp ((cancel_mono E.hom).mp (by simpa only [Category.assoc] using h))
      · exact (GradedObject.isInitialSingleObjApply t (ModuleCat.of F2 F2) n hn).isZero.eq_of_src _ _
    let g := E.inv ≫ e.hom t ≫ E.hom
    have happ (x : F2) : g.hom x = x * g.hom 1 := by
      simpa only [smul_eq_mul,mul_one] using g.hom.map_smul x (1:F2)
    have hc : ∀c:F2, c=0 ∨ c=1 := by decide
    rcases hc (g.hom 1) with h | h
    · have hg : g=0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change g.hom x=0
        rw [happ,h,mul_zero]
      have he : e.hom=0 := by
        apply hj
        change g = E.inv ≫ (0 : L t ⟶ L t) ≫ E.hom
        simpa only [Limits.comp_zero,Limits.zero_comp] using hg
      have hz : (𝟙 L : L ⟶ L)=0 := by
        rw [← e.hom_inv_id, he, Limits.zero_comp]
      have heq := congrArg (fun f:L⟶L => (E.inv ≫ f t ≫ E.hom).hom (1:F2)) hz
      have hzero : (1:F2)=0 := by simp at heq
      exact False.elim (one_ne_zero hzero)
    · apply hj
      have hg : g=𝟙 (ModuleCat.of F2 F2) := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change g.hom x=x
        rw [happ,h,mul_one]
      change g = E.inv ≫ 𝟙 (L t) ≫ E.hom
      simpa only [Category.id_comp,Iso.inv_hom_id] using hg

  have r_trivialIso_unique {M : LeftModule} (t : ℤ) (e f : M ≅ trivialAt t) : e=f := by
    have h := r_lineEndIso_hom t ((GradedModule.forget steenrod).mapIso (e.symm ≪≫ f))
    have hh : e.inv ≫ f.hom = 𝟙 _ := Monad.Algebra.Hom.ext h
    apply Iso.ext
    apply (cancel_epi e.inv).mp
    rw [hh, e.inv_hom_id]
  exact ⟨fun t => ⟨r_shiftDualNatIso t⟩, fun t M e f => r_trivialIso_unique t e f⟩

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite
  HomologicalComplex KIP126.Algebra KIP126.Algebra.GradedVectorSpace
  CategoryTheory.MonoidalCategory KIP126.Algebra.GradedDual
  CategoryTheory.GradedObject.Monoidal CochainComplex.HomComplex in
open scoped TensorProduct in
set_option maxHeartbeats 4000000 in
/-- The comparison fixed on every dual-cobar representative preserves the
two actual Yoneda products.  This is the characteristic-two, same-degree
statement for the fixed Steenrod model; it does not generalize away the
contravariant shift signs over other coefficient fields. -/
theorem preservesYoneda_of_preservesDualCobarRepresentatives (R : Ext.CobarResolution)
    {e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
    (he : PreservesDualCobarRepresentatives R e) : PreservesYoneda e := by
  set_option maxHeartbeats 4000000 in
    exact (by
      set_option backward.isDefEq.respectTransparency false in
        classical
        letI := HasDerivedCategory.standard SourceComodule
        letI := HasDerivedCategory.standard SourceComoduleᵒᵖ
        letI := HasDerivedCategory.standard LeftModule
        let g_opShiftIso (C : Type 1) [Category.{0} C] [Abelian C] (n : ℤ) :
            shiftFunctor (CochainComplex C ℤ)ᵒᵖ n ⋙ (CochainComplex.opEquivalence C).functor ≅
              (CochainComplex.opEquivalence C).functor ⋙ shiftFunctor (CochainComplex Cᵒᵖ ℤ) n := by
          refine NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents
            (fun i => (K.unop.XIsoOfEq (show -(i+n) = -i + -n by omega)).op) ?_) ?_
          · intro i j hij
            apply Quiver.Hom.unop_inj
            change (n.negOnePow • K.unop.d (-(j+n)) (-(i+n))) ≫
                (K.unop.XIsoOfEq (show -(i+n) = -i + -n by omega)).hom =
              (K.unop.XIsoOfEq (show -(j+n) = -j + -n by omega)).hom ≫
                ((-n).negOnePow • K.unop.d (-j + -n) (-i + -n))
            simp only [Int.negOnePow_neg, Linear.units_smul_comp, Linear.comp_units_smul]
            congr 1
            simp
          · intro K L f
            ext i
            apply Quiver.Hom.unop_inj
            change (L.unop.XIsoOfEq (show -(i+n) = -i + -n by omega)).hom ≫
                f.unop.f (-i + -n) =
              f.unop.f (-(i+n)) ≫ (K.unop.XIsoOfEq (show -(i+n) = -i + -n by omega)).hom
            exact (XIsoOfEq_hom_naturality f.unop (show -(i+n) = -i + -n by omega)).symm

        have g_opMap (C : Type 1) [Category.{0} C] [Abelian C] {K L : (CochainComplex C ℤ)ᵒᵖ} (f : K ⟶ L) (i : ℤ) :
            ((CochainComplex.opEquivalence C).functor.map f).f i = (f.unop.f (-i)).op := rfl

        have g_opXIso (C : Type 1) [Category.{0} C] [Abelian C] (K : (CochainComplex C ℤ)ᵒᵖ) {i j : ℤ} (h : i=j) :
            ((CochainComplex.opEquivalence C).functor.obj K).XIsoOfEq h =
              (K.unop.XIsoOfEq (show -j = -i by omega)).op := by
          subst j
          rfl

        letI g_opCommShift (C : Type 1) [Category.{0} C] [Abelian C] : (CochainComplex.opEquivalence C).functor.CommShift ℤ := {
          commShiftIso n := g_opShiftIso C n
          commShiftIso_zero := by
            ext K i
            apply Quiver.Hom.unop_inj
            simp only [g_opShiftIso, NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f,
              Iso.op_hom, Quiver.Hom.unop_op, Functor.CommShift.isoZero_hom_app, HomologicalComplex.comp_f,
              unop_comp, CochainComplex.shiftFunctorZero_inv_app_f, g_opXIso, g_opMap]
            simp [Pretriangulated.shiftFunctorZero_op_hom_app,
              Pretriangulated.shiftFunctorOpIso, CochainComplex.shiftFunctorZero_inv_app_f, XIsoOfEq]
          commShiftIso_add a b := by
            ext K i
            apply Quiver.Hom.unop_inj
            simp only [g_opShiftIso, NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f,
              Iso.op_hom, Quiver.Hom.unop_op, Functor.CommShift.isoAdd_hom_app, HomologicalComplex.comp_f,
              unop_comp, Category.assoc, CochainComplex.shiftFunctorAdd_inv_app_f, g_opXIso, g_opMap,
              CochainComplex.shiftFunctor_map_f']
            have hs := Pretriangulated.shiftFunctorAdd'_op_hom_app K a b (a+b) rfl
              (-a) (-b) (-(a+b)) (by omega) (by omega) (by omega)
            rw [shiftFunctorAdd'_eq_shiftFunctorAdd] at hs
            rw [hs]
            simp only [Pretriangulated.shiftFunctorOpIso, CochainComplex.shiftFunctorAdd'_inv_app_f', XIsoOfEq, eqToIso.hom, eqToIso.inv, eqToHom_refl, NatTrans.id_app, unop_comp, HomologicalComplex.comp_f, Quiver.Hom.unop_op, Category.assoc]
            erw [CategoryTheory.Functor.map_id]
            simp only [CategoryTheory.unop_id, HomologicalComplex.id_f]
            simp only [eqToHom_trans_assoc]
            change eqToHom (congrArg K.unop.X (show -(i+(a+b)) = -i + -(a+b) by omega)) =
              eqToHom (congrArg K.unop.X (show -(i+(a+b)) = (-i + -b) + -a by omega)) ≫
              𝟙 (K.unop.X ((-i + -b) + -a)) ≫ 𝟙 (K.unop.X ((-i + -b) + -a)) ≫
              eqToHom (congrArg K.unop.X (show (-i + -b) + -a = -i + -(a+b) by omega)) ≫
              𝟙 (K.unop.X (-i + -(a+b)))
            simp
        }

        have g_opQuasiIso (C : Type 1) [Category.{0} C] [Abelian C] {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
            QuasiIso ((CochainComplex.opEquivalence C).functor.map f.op) := by
          constructor
          intro n
          rw [quasiIsoAt_iff' _ (n-1) n (n+1) (by simp) (by simp)]
          change ShortComplex.QuasiIso
            (ShortComplex.opMap ((shortComplexFunctor' C (ComplexShape.up ℤ) (-(n+1)) (-n) (-(n-1))).map f))
          rw [ShortComplex.quasiIso_opMap_iff]
          exact (quasiIsoAt_iff' f (-(n+1)) (-n) (-(n-1)) (by simp; omega) (by simp; omega)).mp inferInstance

        let g_opLocalizer (C : Type 1) [Category.{0} C] [Abelian C] :
            LocalizerMorphism (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
              (HomologicalComplex.quasiIso Cᵒᵖ (ComplexShape.up ℤ)) := {
          functor := (CochainComplex.opEquivalence C).functor
          map := by
            intro X Y f hf
            haveI : QuasiIso f.unop := hf
            exact g_opQuasiIso C f.unop
        }

        letI g_opLocalizerCommShift (C : Type 1) [Category.{0} C] [Abelian C] :
            (g_opLocalizer C).functor.CommShift ℤ := g_opCommShift C

        let g_derivedOp (C : Type 1) [Category.{0} C] [Abelian C] [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] :
            (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory Cᵒᵖ :=
          (g_opLocalizer C).localizedFunctor (DerivedCategory.Q (C := C)).op (DerivedCategory.Q (C := Cᵒᵖ))

        letI g_derivedOpCommShift (C : Type 1) [Category.{0} C] [Abelian C] [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] :
            (g_derivedOp C).CommShift ℤ := by dsimp [g_derivedOp]; infer_instance

        let g_opSingleIso (C : Type 1) [Category.{0} C] [Abelian C] (X : C) :
            (CochainComplex.opEquivalence C).functor.obj (Opposite.op ((CochainComplex.singleFunctor C 0).obj X)) ≅
              (CochainComplex.singleFunctor Cᵒᵖ 0).obj (Opposite.op X) := by
          classical
          refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) ?_
          · by_cases hn : n = 0
            · subst n
              exact (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X (-0) (by omega)).symm.op ≪≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Opposite.op X)).symm
            · exact ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X (-n) (by omega)).op).iso
                (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (Opposite.op X) n hn)
          · intro i j hij
            change _ ≫ 0 = 0 ≫ _
            simp

        letI g_derivedOpCommSq (C : Type 1) [Category.{0} C] [Abelian C] [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] :
            CatCommSq (g_opLocalizer C).functor (DerivedCategory.Q (C := C)).op
              (DerivedCategory.Q (C := Cᵒᵖ)) (g_derivedOp C) := by
          dsimp [g_derivedOp]
          exact (g_opLocalizer C).catCommSq (DerivedCategory.Q (C := C)).op (DerivedCategory.Q (C := Cᵒᵖ))

        let g_derivedOpSingleIso (C : Type 1) [Category.{0} C] [Abelian C] [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] (X : C) :
            (g_derivedOp C).obj (Opposite.op ((DerivedCategory.singleFunctor C 0).obj X)) ≅
              (DerivedCategory.singleFunctor Cᵒᵖ 0).obj (Opposite.op X) :=
          (g_derivedOp C).mapIso (((DerivedCategory.singleFunctorIsoCompQ C 0).app X).symm.op) ≪≫
            ((CatCommSq.iso (g_opLocalizer C).functor (DerivedCategory.Q (C := C)).op
              (DerivedCategory.Q (C := Cᵒᵖ)) (g_derivedOp C)).symm.app
                (Opposite.op ((CochainComplex.singleFunctor C 0).obj X))) ≪≫
            DerivedCategory.Q.mapIso (g_opSingleIso C X) ≪≫
            ((DerivedCategory.singleFunctorIsoCompQ Cᵒᵖ 0).app (Opposite.op X)).symm

        let g_extOp (C : Type 1) [Category.{0} C] [Abelian C] [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] [HasExt.{1} C] [HasExt.{1} Cᵒᵖ]
            {X Y : C} {n : ℕ} (x : Abelian.Ext X Y n) :
            Abelian.Ext (Opposite.op Y) (Opposite.op X) n :=
          Abelian.Ext.homEquiv.symm
            ((ShiftedHom.mk₀ _ rfl (g_derivedOpSingleIso C Y).inv).comp
              (((ShiftedHom.opEquiv (n : ℤ) x.hom).map (g_derivedOp C)).comp
                (ShiftedHom.mk₀ _ rfl (g_derivedOpSingleIso C X).hom) (zero_add _)) (add_zero _))

        have g_opEquiv_comp {D : Type 1} [Category.{1} D] [HasShift D ℤ]
            {X Y Z : D} {a b c : ℤ} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
            (h : a+b=c) :
            ShiftedHom.opEquiv c (f.comp g (by omega)) =
              (ShiftedHom.opEquiv b g).comp (ShiftedHom.opEquiv a f) (by omega) := by
          apply (ShiftedHom.opEquiv c).symm.injective
          simpa using (ShiftedHom.opEquiv_symm_comp
            (ShiftedHom.opEquiv b g) (ShiftedHom.opEquiv a f) h).symm

        have g_extOp_comp (C : Type 1) [Category.{0} C] [Abelian C] [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] [HasExt.{1} C] [HasExt.{1} Cᵒᵖ]
            {X Y Z : C} {a b c : ℕ} (x : Abelian.Ext X Y a) (y : Abelian.Ext Y Z b)
            (h : a+b=c) :
            g_extOp C (x.comp y h) = (g_extOp C y).comp (g_extOp C x) (by omega) := by
          apply Abelian.Ext.ext
          simp only [Abelian.Ext.comp_hom, Abelian.Ext.hom, g_extOp, Equiv.apply_symm_apply]
          rw [g_opEquiv_comp x.hom y.hom (show (a : ℤ) + b = c by omega), ShiftedHom.map_comp]
          simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
          simp only [ShiftedHom.comp, Category.assoc, CategoryTheory.Functor.map_comp]
          simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
          rw [← NatTrans.naturality]
          simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]

        have g_cochainOpShifted_f (C : Type 1) [Category.{0} C] [Abelian C] {K L : CochainComplex C ℤ} {n : ℤ}
            (f : ShiftedHom K L n) (i : ℤ) :
            ((ShiftedHom.opEquiv n f).map (CochainComplex.opEquivalence C).functor).f i =
              (L.XIsoOfEq (show -(i+n)+n = -i by omega)).hom.op ≫ (f.f (-(i+n))).op := by
          have hop : ShiftedHom.opEquiv n f =
              (Pretriangulated.opShiftFunctorEquivalence (CochainComplex C ℤ) n).counitIso.inv.app (Opposite.op L) ≫ f.op⟦n⟧' := rfl
          rw [hop]
          simp only [ShiftedHom.map, HomologicalComplex.comp_f,
            CategoryTheory.Functor.map_comp, g_opMap]
          have hc : ((Functor.commShiftIso (CochainComplex.opEquivalence C).functor n).hom.app
              (Opposite.op K)).f i = (K.XIsoOfEq (show -(i+n) = -i + -n by omega)).hom.op := rfl
          rw [hc]
          apply Quiver.Hom.unop_inj
          simp only [unop_comp, Quiver.Hom.unop_op]
          rw [Pretriangulated.opShiftFunctorEquivalence_counitIso_inv_app _ n (-n) (by omega),
            Pretriangulated.shiftFunctor_op_map _ n (-n) (by omega)]
          simp only [Pretriangulated.shiftFunctorOpIso, eqToIso_refl, Iso.refl_inv,
            Iso.refl_hom,
            Quiver.Hom.unop_op]
          simp only [NatTrans.id_app, Category.id_comp,
            unop_comp, Quiver.Hom.unop_op, HomologicalComplex.comp_f,
            CochainComplex.shiftFunctor_map_f']
          erw [unop_id, HomologicalComplex.id_f, Category.id_comp]
          erw [unop_id, HomologicalComplex.id_f, Category.id_comp]
          change (K.XIsoOfEq (show -(i+n) = -i + -n by omega)).hom ≫
            f.f (-i + -n) ≫ ((shiftFunctorCompIsoId (CochainComplex C ℤ) n (-n) (by omega)).hom.app L).f (-i) = _
          simp only [shiftFunctorCompIsoId, Iso.trans_hom, NatTrans.comp_app,
            HomologicalComplex.comp_f,
            CochainComplex.shiftFunctorZero_hom_app_f, Iso.symm_hom,
            CochainComplex.shiftFunctorAdd'_inv_app_f']
          rw [← HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
          simp [HomologicalComplex.XIsoOfEq]

        letI : dualToLeftModule.Additive := by
          constructor
          intro X Y f g
          apply Monad.Algebra.Hom.ext
          funext n
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro φ
          apply LinearMap.ext
          intro x
          change (show Module.Dual F2 (X.unop.A n) from φ)
            ((f.unop.f n).hom x + (g.unop.f n).hom x) = _
          exact map_add _ _ _

        letI : dualToLeftModule.PreservesHomology := by
          let E (n : ℤ) : GrVect F2 ⥤ ModuleCat F2 :=
            (discreteEquivalence F2).functor ⋙ (evaluation (Discrete ℤ) (ModuleCat F2)).obj ⟨n⟩
          letI (n : ℤ) : (E n).Additive := by constructor; intro X Y f g; rfl
          letI (n : ℤ) : PreservesFiniteLimits (E n) := by dsimp [E]; infer_instance
          letI (n : ℤ) : PreservesFiniteColimits (E n) := by dsimp [E]; infer_instance
          let F := Monad.forget (GradedModule.leftTensorMonad steenrod)
          let G := Comonad.forget (GradedComodule.rightTensorComonad Coalgebra.dualSteenrod)
          letI : PreservesFiniteColimits F := ⟨fun _ _ _ => inferInstance⟩
          letI : PreservesFiniteLimits G := ⟨fun _ _ _ => inferInstance⟩
          have graded_exact (S : ShortComplex (GrVect F2))
              (hS : ∀ n : ℤ, (S.map (E n)).Exact) : S.Exact := by
            rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
            funext n
            have hz := (ShortComplex.exact_iff_isZero_homology _).mp (hS n)
            have hh : IsZero ((E n).obj S.homology) :=
              ((S.mapHomologyIso (E n)).isZero_iff).mp hz
            exact hh.eq_of_src _ _
          have dual_zero {A B D : SourceComodule} (f : A ⟶ B) (g : B ⟶ D)
              (w : f ≫ g = 0) : dualLeftMap g ≫ dualLeftMap f = 0 := by
            apply Monad.Algebra.Hom.ext
            funext n
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro φ
            change Module.Dual F2 (D.A n) at φ
            apply LinearMap.ext
            intro x
            have hw := congrArg (fun k => (k.f n).hom x) w
            change φ ((g.f n).hom ((f.f n).hom x)) = 0
            change (g.f n).hom ((f.f n).hom x) = 0 at hw
            rw [hw, map_zero]
          have dual_exact {A B D : SourceComodule} (f : A ⟶ B) (g : B ⟶ D)
              (w : f ≫ g = 0) (h : (ShortComplex.mk f g w).Exact) :
              (ShortComplex.mk (dualLeftMap g) (dualLeftMap f) (dual_zero f g w)).Exact := by
            apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
            apply graded_exact
            intro n
            have hn := (h.map G).map (E n)
            apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
            change LinearMap.range (g.f n).hom.dualMap = LinearMap.ker (f.f n).hom.dualMap
            rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
              LinearMap.ker_dualMap_eq_dualAnnihilator_range]
            exact congrArg Submodule.dualAnnihilator hn.moduleCat_range_eq_ker.symm
          apply Functor.preservesHomology_of_map_exact
          intro S hS
          have hu := (ShortComplex.exact_unop_iff S).mpr hS
          exact dual_exact S.g.unop S.f.unop S.unop.zero hu

        letI : PreservesFiniteLimits dualToLeftModule :=
          Functor.preservesFiniteLimits_of_preservesHomology dualToLeftModule

        letI : PreservesFiniteColimits dualToLeftModule :=
          Functor.preservesFiniteColimits_of_preservesHomology dualToLeftModule

        letI : HasExt.{1} SourceComoduleᵒᵖ := HasExt.standard _

        let dualExt {X Y : SourceComodule} {n : ℕ}
            (x : Abelian.Ext X Y n) : Abelian.Ext (dualLeftModule Y) (dualLeftModule X) n :=
          (g_extOp SourceComodule x).mapExactFunctor dualToLeftModule

        have dualExt_comp {X Y Z : SourceComodule} {a b c : ℕ}
            (x : Abelian.Ext X Y a) (y : Abelian.Ext Y Z b) (h : a+b=c) :
            dualExt (x.comp y h) = (dualExt y).comp (dualExt x) (by omega) := by
          dsimp only [dualExt]
          rw [g_extOp_comp, Abelian.Ext.mapExactFunctor_comp]

        let dualCochain (R : Ext.CobarResolution) : CochainComplex LeftModule ℤ :=
          (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.opEquivalence SourceComodule).functor.obj (Opposite.op R.resolution.cochainComplex))

        let dualCochainIso (R : Ext.CobarResolution) :
            (dualCobarResolution R).cochainComplex ≅ dualCochain R := by
          classical
          refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) ?_
          · by_cases hn : n ≤ 0
            · exact (dualCobarResolution R).cochainComplexXIso n (-n).toNat (by omega) ≪≫
                dualToLeftModule.mapIso ((R.resolution.cochainComplexXIso (-n) (-n).toNat (by omega)).op)
            · exact (CochainComplex.isZero_of_isStrictlyLE (dualCobarResolution R).cochainComplex 0 n (by omega)).iso
                (dualToLeftModule.map_isZero
                  (CochainComplex.isZero_of_isStrictlyGE R.resolution.cochainComplex 0 (-n) (by omega)).op)
          · intro i j hij
            by_cases hi : i ≤ 0
            · by_cases hj : j ≤ 0
              · simp only [dif_pos hi, dif_pos hj, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
                rw [(dualCobarResolution R).cochainComplex_d i j (-i).toNat (-j).toNat (by omega) (by omega)]
                change _ ≫ dualToLeftModule.map (R.resolution.cochainComplex.d (-j) (-i)).op = _
                rw [R.resolution.cochainComplex_d (-j) (-i) (-j).toNat (-i).toNat (by omega) (by omega)]
                simp only [op_comp, Functor.map_comp, Category.assoc]
                rw [← Functor.map_comp_assoc, ← op_comp, Iso.inv_hom_id]
                simp only [op_id, Iso.inv_hom_id_assoc]
                rfl
              · exact (dualToLeftModule.map_isZero
                  (CochainComplex.isZero_of_isStrictlyGE R.resolution.cochainComplex 0 (-j) (by omega)).op).eq_of_tgt _ _
            · exact (CochainComplex.isZero_of_isStrictlyLE (dualCobarResolution R).cochainComplex 0 i (by omega)).eq_of_src _ _

        let dualSingleIso (X : SourceComodule) :
            (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((CochainComplex.opEquivalence SourceComodule).functor.obj
                (Opposite.op ((CochainComplex.singleFunctor SourceComodule 0).obj X))) ≅
              (CochainComplex.singleFunctor LeftModule 0).obj (dualLeftModule X) :=
          (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
            (g_opSingleIso SourceComodule X) ≪≫
          (dualToLeftModule.mapCochainComplexSingleFunctor 0).app (Opposite.op X)

        have dualAugmentation (R : Ext.CobarResolution) :
            (dualCochainIso R).hom ≫
              (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ)).map
                ((CochainComplex.opEquivalence SourceComodule).functor.map R.resolution.ι'.op) ≫
              (dualSingleIso (Ext.trivialAt 0)).hom ≫
              (CochainComplex.singleFunctor LeftModule 0).map (trivialDualIso 0).hom =
            (dualCobarResolution R).π' := by
          apply HomologicalComplex.Hom.ext
          funext n
          by_cases hn : n = 0
          · subst n
            simp only [HomologicalComplex.comp_f, ProjectiveResolution.π'_f_zero,
              dualCochainIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
              dif_pos (show (0 : ℤ) ≤ 0 by omega), Iso.trans_hom, Functor.mapIso_hom,
              Iso.op_hom]
            simp only [dualSingleIso, Iso.trans_hom, HomologicalComplex.comp_f,
              Functor.mapIso_hom, Functor.mapHomologicalComplex_map_f,
              Functor.mapCochainComplexSingleFunctor]
            simp only [Iso.app_hom, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
              g_opMap, Int.neg_zero, Int.toNat_zero,
              g_opSingleIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
              CochainComplex.singleFunctor, CochainComplex.singleFunctors,
              HomologicalComplex.single_map_f_self]
            simp only [Quiver.Hom.unop_op, dif_pos True.intro, InjectiveResolution.ι'_f_zero,
              Iso.trans_hom, Iso.op_hom, Iso.symm_hom, op_comp, Functor.map_comp,
              Category.assoc]
            simp only [HomologicalComplex.singleObjXSelf, ← Functor.map_comp_assoc, Iso.inv_hom_id]
            simp only [← op_comp_assoc, Category.comp_id]
            erw [Iso.inv_hom_id_assoc]
            simp only [← op_comp, Category.assoc, Iso.inv_hom_id_assoc]
            simp only [Iso.inv_hom_id, Category.comp_id]
            simp only [dualCobarResolution, dualCobarAugmentation, dualCobarAugmentationZero,
              ChainComplex.toSingle₀Equiv_symm_apply_f_zero, Category.assoc]
            rfl
          · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (trivialAt 0) n hn).eq_of_tgt _ _

        have dualCocycle (R : Ext.CobarResolution) (s : ℕ) (t : ℤ)
            (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s)
            (hf : f ≫ R.resolution.cocomplex.d s (s+1) = 0)
            (hf' : (dualCobarResolution R).complex.d (s+1) s ≫
              (dualLeftMap f ≫ (trivialDualIso t).hom) = 0) :
            let α := Cocycle.equivHomShift.symm (Cocycle.fromSingleMk
              (f ≫ (R.resolution.cochainComplexXIso s s rfl).inv) (zero_add _)
              (s+1) (by omega) (by simp [R.resolution.cochainComplex_d (s : ℤ) (s+1) s (s+1) rfl (by omega), reassoc_of% hf]))
            let β := Cocycle.equivHomShift.symm (Cocycle.toSingleMk
              (((dualCobarResolution R).cochainComplexXIso (-s) s rfl).hom ≫
                (dualLeftMap f ≫ (trivialDualIso t).hom)) (by simp)
              (-(s+1)) (by omega) (by simpa [ProjectiveResolution.cochainComplex_d (dualCobarResolution R) (-(s+1)) (-s) (s+1) s (by omega) rfl, Category.assoc, reassoc_of% hf']))
            (ShiftedHom.mk₀ 0 rfl (dualCochainIso R).hom).comp
              ((((ShiftedHom.opEquiv (s : ℤ) α).map (CochainComplex.opEquivalence SourceComodule).functor).map
                (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ))).comp
                (ShiftedHom.mk₀ 0 rfl ((dualSingleIso (Ext.trivialAt t)).hom ≫
                  (CochainComplex.singleFunctor LeftModule 0).map (trivialDualIso t).hom)) (zero_add _)) (add_zero _) = β := by
          have hmap {K L : CochainComplex SourceComoduleᵒᵖ ℤ} {n : ℤ}
              (g : ShiftedHom K L n) (i : ℤ) :
              (g.map (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ))).f i =
                dualToLeftModule.map (g.f i) := by
            simp only [ShiftedHom.map, HomologicalComplex.comp_f,
              Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
            erw [Category.comp_id]
          dsimp only
          simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
          apply HomologicalComplex.Hom.ext
          funext i
          by_cases hi : i + (s : ℤ) = 0
          · have hi' : i = -(s : ℤ) := by omega
            subst i
            simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f', hmap,
              g_cochainOpShifted_f]
            simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
              Cocycle.rightShift_coe, Cochain.rightShift, Cochain.mk_v,
              Cocycle.fromSingleMk_coe, Cocycle.toSingleMk_coe]
            simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
              eqToIso.hom, eqToIso.inv]
            simp only [eqToHom_refl, Category.comp_id]
            simp only [Cochain.fromSingleMk, Cochain.toSingleMk, Cochain.single, Cochain.mk_v]
            rw [dif_pos (show (0 : ℤ) = -(-s+s) ∧ (s : ℤ) = -(-s+s)+s by omega),
              dif_pos (show True ∧ (0 : ℤ) = -s+s by exact ⟨True.intro, by omega⟩)]
            apply (cancel_mono (((CochainComplex.singleFunctor LeftModule 0).obj (trivialAt t)).XIsoOfEq hi).hom).mp
            simp only [Category.assoc]
            rw [HomologicalComplex.XIsoOfEq_hom_naturality
              ((CochainComplex.singleFunctor LeftModule 0).map (trivialDualIso t).hom) hi]
            rw [HomologicalComplex.XIsoOfEq_hom_naturality_assoc (dualSingleIso (Ext.trivialAt t)).hom hi]
            have hmapXI (K : CochainComplex SourceComoduleᵒᵖ ℤ) {a b : ℤ} (h : a=b) :
                ((dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).XIsoOfEq h =
                  dualToLeftModule.mapIso (K.XIsoOfEq h) := by
              subst b
              rfl
            rw [hmapXI, g_opXIso]
            simp only [Functor.mapIso_hom, Iso.op_hom, Int.neg_zero]
            simp only [← Functor.map_comp_assoc, ← op_comp, Category.assoc,
              HomologicalComplex.XIsoOfEq, eqToIso.hom, eqToIso.inv,
              eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
            have hPi : (dualCochainIso R).hom.f (-s) =
                ((dualCobarResolution R).cochainComplexXIso (-s) s rfl).hom ≫
                  dualToLeftModule.map (R.resolution.cochainComplexXIso (-(-s)) s (by omega)).hom.op := by
              simp [dualCochainIso]
              have haux (a b : ℕ) (ha : -(a : ℤ) = -s) (hb : -(b : ℤ) = -s) (hab : a=b) :
                  ((dualCobarResolution R).cochainComplexXIso (-s) a ha).hom ≫
                      dualToLeftModule.map (R.resolution.cochainComplexXIso (-(-s)) a (by omega)).hom.op =
                  ((dualCobarResolution R).cochainComplexXIso (-s) b hb).hom ≫
                      dualToLeftModule.map (R.resolution.cochainComplexXIso (-(-s)) b (by omega)).hom.op := by
                subst b
                rfl
              exact haux _ _ _ _ (by omega)
            rw [hPi]
            simp only [eqToHom_trans]
            have hcoh (n : ℤ) (hn : (s : ℤ) = n) :
                (R.resolution.cochainComplexXIso s s rfl).inv ≫
                  eqToHom (congrArg R.resolution.cochainComplex.X hn) ≫
                    (R.resolution.cochainComplexXIso n s hn).hom = 𝟙 _ := by
              subst n
              simp
            simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, Category.assoc]
            rw [hcoh (-(-s)) (by omega)]
            simp only [Category.comp_id]
            erw [eqToHom_refl]
            simp only [Category.comp_id]
            have hsingle (X : SourceComodule) :
                dualToLeftModule.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom.op ≫
                  (dualSingleIso X).hom.f 0 =
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (dualLeftModule X)).inv := by
              simp only [dualSingleIso, Iso.trans_hom, HomologicalComplex.comp_f,
                Functor.mapIso_hom, Functor.mapHomologicalComplex_map_f,
                Functor.mapCochainComplexSingleFunctor, Iso.app_hom,
                HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
                g_opSingleIso, HomologicalComplex.Hom.isoOfComponents_hom_f, dif_pos True.intro, Iso.symm_hom, Iso.op_hom, Int.neg_zero]
              simp only [HomologicalComplex.singleObjXSelf, Functor.map_comp, Category.assoc]
              simp only [← Functor.map_comp_assoc, ← op_comp_assoc, Iso.inv_hom_id,
                op_id, Category.id_comp]
              erw [CategoryTheory.Functor.map_id, Category.id_comp]
              rfl
            rw [op_comp, Functor.map_comp]
            simp only [Category.assoc]
            rw [reassoc_of% (hsingle (Ext.trivialAt t))]
            simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
              HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
            rfl
          · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (trivialAt t) (i+s) hi).eq_of_tgt _ _

        let dualDerived : (DerivedCategory SourceComodule)ᵒᵖ ⥤ DerivedCategory LeftModule :=
          g_derivedOp SourceComodule ⋙ dualToLeftModule.mapDerivedCategory

        letI : dualDerived.CommShift ℤ := by
          dsimp [dualDerived]
          infer_instance

        let dualDerivedSingle (X : SourceComodule) :
            dualDerived.obj (Opposite.op ((DerivedCategory.singleFunctor SourceComodule 0).obj X)) ≅
              (DerivedCategory.singleFunctor LeftModule 0).obj (dualLeftModule X) :=
          dualToLeftModule.mapDerivedCategory.mapIso (g_derivedOpSingleIso SourceComodule X) ≪≫
            (dualToLeftModule.mapDerivedCategorySingleFunctor 0).app (Opposite.op X)

        have dualExt_hom {X Y : SourceComodule} {n : ℕ} (x : Abelian.Ext X Y n) :
            (dualExt x).hom =
              (ShiftedHom.mk₀ 0 rfl (dualDerivedSingle Y).inv).comp
                (((ShiftedHom.opEquiv (n:ℤ) x.hom).map dualDerived).comp
                  (ShiftedHom.mk₀ 0 rfl (dualDerivedSingle X).hom) (zero_add _)) (add_zero _) := by
          dsimp only [dualExt]
          rw [Abelian.Ext.mapExactFunctor_hom]
          simp only [g_extOp, Abelian.Ext.hom, Equiv.apply_symm_apply,
            ShiftedHom.map_comp, ShiftedHom.map_mk₀]
          simp only [dualDerived, ShiftedHom.comp_map, dualDerivedSingle,
            Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
            ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Functor.map_comp, Category.assoc]
          rfl

        let dualDerivedFactors :
            (DerivedCategory.Q (C := SourceComodule)).op ⋙ dualDerived ≅
              (CochainComplex.opEquivalence SourceComodule).functor ⋙
                dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight ((CatCommSq.iso (g_opLocalizer SourceComodule).functor
              (DerivedCategory.Q (C := SourceComodule)).op (DerivedCategory.Q (C := SourceComoduleᵒᵖ))
                (g_derivedOp SourceComodule)).symm) dualToLeftModule.mapDerivedCategory ≪≫
              Functor.associator _ _ _ ≪≫
                Functor.isoWhiskerLeft (CochainComplex.opEquivalence SourceComodule).functor
                  dualToLeftModule.mapDerivedCategoryFactors

        letI dualDerivedFactorsCommShift : NatTrans.CommShift dualDerivedFactors.hom ℤ := by
          haveI : NatTrans.CommShift (CatCommSq.iso (g_opLocalizer SourceComodule).functor
              (DerivedCategory.Q (C := SourceComodule)).op (DerivedCategory.Q (C := SourceComoduleᵒᵖ))
                (g_derivedOp SourceComodule)).hom ℤ :=
            (g_opLocalizer SourceComodule).natTransCommShift_hom (M := ℤ)
              (DerivedCategory.Q (C := SourceComodule)).op (DerivedCategory.Q (C := SourceComoduleᵒᵖ))
              (g_derivedOp SourceComodule) (CatCommSq.iso ..)
          simp only [dualDerivedFactors, Iso.trans_hom, Iso.symm_hom,
            Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
          infer_instance

        have dualDerivedFactors_shifted {X Y : (CochainComplex SourceComodule ℤ)ᵒᵖ}
            {n : ℤ} (f : ShiftedHom X Y n) :
            (ShiftedHom.mk₀ 0 rfl (dualDerivedFactors.inv.app X)).comp
              (((f.map (DerivedCategory.Q (C := SourceComodule)).op).map dualDerived).comp
                (ShiftedHom.mk₀ 0 rfl (dualDerivedFactors.hom.app Y)) (zero_add _)) (add_zero _) =
              ((f.map (CochainComplex.opEquivalence SourceComodule).functor).map
                (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ))).map DerivedCategory.Q := by
          simpa only [ShiftedHom.comp_map] using ShiftedHom.map_naturality_1 f dualDerivedFactors

        have opEquiv_map {C D : Type 1} [Category.{0} C] [Category.{1} D]
            [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
            {X Y : C} {n : ℤ} (f : ShiftedHom X Y n) :
            ShiftedHom.opEquiv n (f.map F) = (ShiftedHom.opEquiv n f).map F.op := by
          obtain ⟨g,rfl⟩ := (ShiftedHom.opEquiv n).symm.surjective f
          rw [Equiv.apply_symm_apply]
          apply (ShiftedHom.opEquiv n).symm.injective
          simp only [Equiv.symm_apply_apply,
            ShiftedHom.opEquiv_symm_apply, ShiftedHom.map,
            CategoryTheory.Functor.map_comp, CategoryTheory.Functor.op_map,
            unop_comp, Quiver.Hom.unop_op, Category.assoc,
            CategoryTheory.Functor.map_opShiftFunctorEquivalence_unitIso_inv_app_unop]
          rw [CategoryTheory.Functor.commShiftIso_hom_naturality]
          erw [Category.assoc, Iso.inv_hom_id_app_assoc]
          simp only [Pretriangulated.opShiftFunctorEquivalence, Iso.trans_inv,
            NatTrans.comp_app, unop_comp, Category.assoc]

        have dualDerivedFactors_opShifted {X Y : CochainComplex SourceComodule ℤ}
            {n : ℤ} (f : ShiftedHom X Y n) :
            (ShiftedHom.mk₀ 0 rfl (dualDerivedFactors.inv.app (Opposite.op Y))).comp
              (((ShiftedHom.opEquiv n (f.map DerivedCategory.Q)).map dualDerived).comp
                (ShiftedHom.mk₀ 0 rfl (dualDerivedFactors.hom.app (Opposite.op X))) (zero_add _)) (add_zero _) =
              (((ShiftedHom.opEquiv n f).map (CochainComplex.opEquivalence SourceComodule).functor).map
                (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ))).map DerivedCategory.Q := by
          rw [opEquiv_map]
          exact dualDerivedFactors_shifted _

        have dualDerivedFactors_single (X : SourceComodule) :
            dualDerivedFactors.hom.app (Opposite.op ((CochainComplex.singleFunctor SourceComodule 0).obj X)) ≫
                DerivedCategory.Q.map (dualSingleIso X).hom =
              dualDerived.map (((DerivedCategory.singleFunctorIsoCompQ SourceComodule 0).app X).hom.op) ≫
                (dualDerivedSingle X).hom ≫
                  ((DerivedCategory.singleFunctorIsoCompQ LeftModule 0).app (dualLeftModule X)).hom := by
          simp only [dualDerivedFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
            Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
            Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
            Functor.whiskerLeft_app, dualDerivedSingle, Functor.mapIso_hom, Iso.app_hom,
            g_derivedOpSingleIso, Functor.map_comp,
            Iso.app_inv, Iso.symm_hom, Iso.op_hom, Category.assoc]
          simp only [dualDerived, Functor.comp_map, ← Functor.map_comp_assoc, ← op_comp, Category.id_comp]
          dsimp only [dualSingleIso]
          rw [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
          simp only [Iso.inv_hom_id_app, op_id,
            Functor.map_comp, Category.assoc]
          erw [(g_derivedOp SourceComodule).map_id,
            dualToLeftModule.mapDerivedCategory.map_id, Category.id_comp]
          congr 1
          rw [← Category.assoc]
          erw [← dualToLeftModule.mapDerivedCategoryFactors_hom_naturality
            (g_opSingleIso SourceComodule X).hom]
          simp only [Category.assoc]
          congr 1
          simp only [Functor.mapDerivedCategorySingleFunctor, Iso.app_hom, Iso.trans_hom,
            NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
            Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
            Functor.associator_inv_app, Iso.symm_hom, Category.id_comp,
            Category.assoc]
          simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
          simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
          erw [dualToLeftModule.mapDerivedCategory.map_id, Category.id_comp]
          rfl

        let dualCoeff {s : ℕ} {t : ℤ} (x : Ext.SphereExt s t) : SphereExt s t :=
          (Abelian.Ext.mk₀ (trivialDualIso 0).inv).comp
            ((dualExt x).comp (Abelian.Ext.mk₀ (trivialDualIso t).hom) (Nat.add_zero _)) (Nat.zero_add _)

        have dualRepresentative_prefix (R : Ext.CobarResolution) :
            (DerivedCategory.singleFunctor LeftModule 0).map (trivialDualIso 0).inv ≫
              (dualDerivedSingle (Ext.trivialAt 0)).inv ≫
              dualDerived.map (((DerivedCategory.singleFunctorIsoCompQ SourceComodule 0).app (Ext.trivialAt 0)).inv.op) ≫
              dualDerived.map ((inv (DerivedCategory.Q.map R.resolution.ι')).op) ≫
              dualDerivedFactors.hom.app (Opposite.op R.resolution.cochainComplex) =
            ((DerivedCategory.singleFunctorIsoCompQ LeftModule 0).app (trivialAt 0)).hom ≫
              inv (DerivedCategory.Q.map (dualCobarResolution R).π') ≫
              DerivedCategory.Q.map (dualCochainIso R).hom := by
          have hn := dualDerivedFactors.hom.naturality R.resolution.ι'.op
          simp only [Functor.comp_map, Functor.op_map] at hn
          have ha := congrArg (fun f => DerivedCategory.Q.map f) (dualAugmentation R)
          simp only [Functor.map_comp] at ha
          apply (cancel_mono (DerivedCategory.Q.map (dualCochainIso R).inv ≫
            DerivedCategory.Q.map (dualCobarResolution R).π')).mp
          simp only [Category.assoc]
          have hc : DerivedCategory.Q.map (dualCochainIso R).hom ≫
              DerivedCategory.Q.map (dualCochainIso R).inv = 𝟙 _ := by
            rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
          rw [reassoc_of% hc]
          simp only [IsIso.inv_hom_id, Category.comp_id]
          have hc' : DerivedCategory.Q.map (dualCochainIso R).inv ≫
              DerivedCategory.Q.map (dualCochainIso R).hom = 𝟙 _ := by
            rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
          rw [← ha]
          erw [reassoc_of% hc']
          erw [← reassoc_of% hn]
          have hd : dualDerived.map ((inv (DerivedCategory.Q.map R.resolution.ι')).op) ≫
              dualDerived.map (DerivedCategory.Q.map R.resolution.ι').op = 𝟙 _ := by
            rw [← Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id, CategoryTheory.Functor.map_id]
          erw [reassoc_of% hd]
          rw [reassoc_of% (dualDerivedFactors_single (Ext.trivialAt 0))]
          have hdS : dualDerived.map (((DerivedCategory.singleFunctorIsoCompQ SourceComodule 0).app (Ext.trivialAt 0)).inv.op) ≫
              dualDerived.map (((DerivedCategory.singleFunctorIsoCompQ SourceComodule 0).app (Ext.trivialAt 0)).hom.op) = 𝟙 _ := by
            rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id, CategoryTheory.Functor.map_id]
          erw [reassoc_of% hdS, Iso.inv_hom_id_assoc]
          have hs := (DerivedCategory.singleFunctorIsoCompQ LeftModule 0).hom.naturality (trivialDualIso 0).hom
          dsimp only [Functor.comp_map] at hs
          erw [← hs]
          simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
          rfl

        have dualRepresentative_suffix (t : ℤ) :
            dualDerived.map (((DerivedCategory.singleFunctorIsoCompQ SourceComodule 0).app (Ext.trivialAt t)).hom.op) ≫
              (dualDerivedSingle (Ext.trivialAt t)).hom ≫
              (DerivedCategory.singleFunctor LeftModule 0).map (trivialDualIso t).hom =
            dualDerivedFactors.hom.app (Opposite.op ((CochainComplex.singleFunctor SourceComodule 0).obj (Ext.trivialAt t))) ≫
              DerivedCategory.Q.map (dualSingleIso (Ext.trivialAt t)).hom ≫
              DerivedCategory.Q.map ((CochainComplex.singleFunctor LeftModule 0).map (trivialDualIso t).hom) ≫
              ((DerivedCategory.singleFunctorIsoCompQ LeftModule 0).app (trivialAt t)).inv := by
          rw [reassoc_of% (dualDerivedFactors_single (Ext.trivialAt t))]
          have hs := (DerivedCategory.singleFunctorIsoCompQ LeftModule 0).hom.naturality (trivialDualIso t).hom
          dsimp only [Functor.comp_map] at hs
          erw [← reassoc_of% hs]
          erw [Iso.hom_inv_id_app]
          simp only [Category.comp_id]

        have opEquiv_mk₀ {C : Type 1} [Category.{1} C] [HasShift C ℤ] {X Y : C} (f : X ⟶ Y) :
            ShiftedHom.opEquiv 0 (ShiftedHom.mk₀ 0 rfl f) = ShiftedHom.mk₀ 0 rfl f.op := by
          apply (ShiftedHom.opEquiv 0).symm.injective
          simp only [Equiv.symm_apply_apply, ShiftedHom.opEquiv_symm_apply,
            ShiftedHom.mk₀, shiftFunctorZero',
            Pretriangulated.opShiftFunctorEquivalence_zero_unitIso_inv_app]
          simp only [eqToIso_refl, Iso.refl_trans, unop_comp, Quiver.Hom.unop_op,
            CategoryTheory.Functor.map_comp, Category.assoc]
          simp only [← CategoryTheory.Functor.map_comp_assoc, ← unop_comp, Iso.inv_hom_id_app]
          simp only [CategoryTheory.Functor.id_obj, unop_id, CategoryTheory.Functor.map_id, Category.id_comp]
          exact (shiftFunctorZero C ℤ).inv.naturality f

        have dualDerivedFactors_opShifted_inv {X Y : CochainComplex SourceComodule ℤ}
            {n : ℤ} (f : ShiftedHom X Y n) :
            (ShiftedHom.mk₀ 0 rfl (dualDerivedFactors.hom.app (Opposite.op Y))).comp
              (((((ShiftedHom.opEquiv n f).map (CochainComplex.opEquivalence SourceComodule).functor).map
                  (dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ))).map DerivedCategory.Q).comp
                (ShiftedHom.mk₀ 0 rfl (dualDerivedFactors.inv.app (Opposite.op X))) (zero_add _)) (add_zero _) =
              (ShiftedHom.opEquiv n (f.map DerivedCategory.Q)).map dualDerived := by
          rw [opEquiv_map]
          simpa only [ShiftedHom.comp_map] using ShiftedHom.map_naturality_2 (ShiftedHom.opEquiv n f) dualDerivedFactors

        have dualCoeff_extMk (R : Ext.CobarResolution) (s : ℕ) (t : ℤ)
            (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s)
            (hf : f ≫ R.resolution.cocomplex.d s (s+1) = 0)
            (hf' : (dualCobarResolution R).complex.d (s+1) s ≫
              (dualLeftMap f ≫ (trivialDualIso t).hom) = 0) :
            dualCoeff (R.resolution.extMk f (s+1) rfl hf) =
              (dualCobarResolution R).extMk (dualLeftMap f ≫ (trivialDualIso t).hom) (s+1) rfl hf' := by
          apply Abelian.Ext.ext
          simp only [dualCoeff, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, dualExt_hom,
            InjectiveResolution.extMk_hom, ProjectiveResolution.extMk_hom]
          rw [g_opEquiv_comp _ _ (by omega),
            g_opEquiv_comp _ _ (by omega)]
          simp only [opEquiv_mk₀, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
          erw [← dualDerivedFactors_opShifted_inv]
          simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
            Functor.map_comp, Category.assoc, op_comp]
          have hb := congrArg (fun g => ShiftedHom.map g (DerivedCategory.Q (C := LeftModule)))
            (dualCocycle R s t f hf hf')
          simp only [ShiftedHom.map_comp, ShiftedHom.map_mk₀] at hb
          simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Functor.map_comp] at hb
          erw [← hb]
          erw [reassoc_of% (dualRepresentative_prefix R)]
          have hs := congrArg (fun g => (shiftFunctor (DerivedCategory LeftModule) (s : ℤ)).map g)
            (dualRepresentative_suffix t)
          simp only [Functor.map_comp] at hs
          erw [hs]
          have hc := ((shiftFunctor (DerivedCategory LeftModule) (s : ℤ)).mapIso
            (dualDerivedFactors.app (Opposite.op ((CochainComplex.singleFunctor SourceComodule 0).obj (Ext.trivialAt t))))).inv_hom_id
          simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom] at hc
          erw [reassoc_of% hc]
          simp only [Nat.cast_add, Nat.cast_one, Category.assoc]
          rfl

        have comparison_eq_dualCoeff (R : Ext.CobarResolution)
            {e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
            (he : PreservesDualCobarRepresentatives R e) (s : ℕ) (t : ℤ) (x : Ext.SphereExt s t) :
            e s t x = dualCoeff x := by
          obtain ⟨f, hf, rfl⟩ := R.resolution.extMk_surjective x (s+1) rfl
          obtain ⟨hf', h⟩ := he s t f hf
          exact h.trans (dualCoeff_extMk R s t f hf hf').symm

        have g_opSingle_naturality {C : Type 1} [Category.{0} C] [Abelian C]
            {X Y : C} (f : X ⟶ Y) :
            (CochainComplex.opEquivalence C).functor.map
              ((CochainComplex.singleFunctor C 0).map f).op ≫ (g_opSingleIso C X).hom =
            (g_opSingleIso C Y).hom ≫ (CochainComplex.singleFunctor Cᵒᵖ 0).map f.op := by
          ext n
          by_cases hn : n = 0
          · subst n
            dsimp [g_opSingleIso, HomologicalComplex.singleObjXSelf,
              HomologicalComplex.singleObjXIsoOfEq, CochainComplex.singleFunctor,
              CochainComplex.singleFunctors, HomologicalComplex.single]
            simp
            erw [g_opMap]
            simp
            exact (Category.comp_id f.op).trans (Category.id_comp f.op).symm
          · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (Opposite.op X) n hn).eq_of_tgt _ _

        have g_derivedOpSingle_naturality {C : Type 1} [Category.{0} C] [Abelian C]
            [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ]
            {X Y : C} (f : X ⟶ Y) :
            (g_derivedOp C).map ((DerivedCategory.singleFunctor C 0).map f).op ≫ (g_derivedOpSingleIso C X).hom =
              (g_derivedOpSingleIso C Y).hom ≫ (DerivedCategory.singleFunctor Cᵒᵖ 0).map f.op := by
          simp only [g_derivedOpSingleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
          simp only [DerivedCategory.singleFunctorIsoCompQ]
          simp only [Iso.refl_inv, NatTrans.id_app]
          erw [(g_derivedOp C).map_id, (g_derivedOp C).map_id]
          simp only [Category.id_comp]
          rw [← Category.assoc]
          erw [((CatCommSq.iso (g_opLocalizer C).functor (DerivedCategory.Q (C := C)).op
              (DerivedCategory.Q (C := Cᵒᵖ)) (g_derivedOp C)).inv).naturality]
          dsimp only [Functor.comp_map, Functor.op_map]
          simp only [Category.assoc]
          congr 1
          erw [Category.comp_id, Category.id_comp]
          change DerivedCategory.Q.map ((CochainComplex.opEquivalence C).functor.map
            ((CochainComplex.singleFunctor C 0).map f).op) ≫ DerivedCategory.Q.map (g_opSingleIso C X).hom =
            DerivedCategory.Q.map (g_opSingleIso C Y).hom ≫
              DerivedCategory.Q.map ((CochainComplex.singleFunctor Cᵒᵖ 0).map f.op)
          rw [← Functor.map_comp, ← Functor.map_comp, g_opSingle_naturality]

        have g_opEquiv_mk₀ {C : Type 1} [Category.{1} C] [HasShift C ℤ] {X Y : C} (f : X ⟶ Y) :
            ShiftedHom.opEquiv 0 (ShiftedHom.mk₀ 0 rfl f) = ShiftedHom.mk₀ 0 rfl f.op := by
          apply (ShiftedHom.opEquiv 0).symm.injective
          simp only [Equiv.symm_apply_apply, ShiftedHom.opEquiv_symm_apply,
            ShiftedHom.mk₀, shiftFunctorZero',
            Pretriangulated.opShiftFunctorEquivalence_zero_unitIso_inv_app]
          simp only [eqToIso_refl, Iso.refl_trans, unop_comp, Quiver.Hom.unop_op,
            Functor.map_comp, Category.assoc]
          simp only [← Functor.map_comp_assoc, ← unop_comp, Iso.inv_hom_id_app]
          simp only [Functor.id_obj, unop_id]
          erw [(shiftFunctor C (0:ℤ)).map_id, Category.id_comp]
          exact (shiftFunctorZero C ℤ).inv.naturality f

        have g_extOp_mk₀ {C : Type 1} [Category.{0} C] [Abelian C]
            [HasDerivedCategory.{1} C] [HasDerivedCategory.{1} Cᵒᵖ] [HasExt.{1} C] [HasExt.{1} Cᵒᵖ]
            {X Y : C} (f : X ⟶ Y) : g_extOp C (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ f.op := by
          apply Abelian.Ext.ext
          simp only [g_extOp, Abelian.Ext.hom, Equiv.apply_symm_apply, Abelian.Ext.mk₀_hom]
          erw [g_opEquiv_mk₀, ShiftedHom.map_mk₀]
          simp only [ShiftedHom.mk₀_comp_mk₀]
          congr 1
          rw [g_derivedOpSingle_naturality, Iso.inv_hom_id_assoc]

        have dualExt_mk₀ {X Y : SourceComodule} (f : X ⟶ Y) :
            dualExt (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (dualLeftMap f) := by
          dsimp only [dualExt]
          rw [g_extOp_mk₀, Abelian.Ext.mapExactFunctor_mk₀]
          rfl

        let r_shiftDualNatIso (t : ℤ) :
            (GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).op ⋙ dualToLeftModule ≅
              dualToLeftModule ⋙ GradedModule.internalShift F2 steenrod t :=
          Classical.choice (dualShift_exists_unique.1 t)
        let r_shiftDualModuleIso (M : SourceComodule) (t : ℤ) :
            dualLeftModule ((GradedComodule.internalShift F2 Coalgebra.dualSteenrod t).obj M) ≅
              (GradedModule.internalShift F2 steenrod t).obj (dualLeftModule M) :=
          (r_shiftDualNatIso t).app (Opposite.op M)
        have r_trivialIso_unique {M : LeftModule} (t : ℤ) (e f : M ≅ trivialAt t) : e=f :=
          dualShift_exists_unique.2 t e f

        have opEquiv_map_derived {C D : Type 1} [Category.{1} C] [Category.{1} D]
            [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
            {X Y : C} {n : ℤ} (f : ShiftedHom X Y n) :
            ShiftedHom.opEquiv n (f.map F) = (ShiftedHom.opEquiv n f).map F.op := by
          obtain ⟨g,rfl⟩ := (ShiftedHom.opEquiv n).symm.surjective f
          rw [Equiv.apply_symm_apply]
          apply (ShiftedHom.opEquiv n).symm.injective
          simp only [Equiv.symm_apply_apply,
            ShiftedHom.opEquiv_symm_apply, ShiftedHom.map,
            CategoryTheory.Functor.map_comp, CategoryTheory.Functor.op_map,
            unop_comp, Quiver.Hom.unop_op, Category.assoc,
            CategoryTheory.Functor.map_opShiftFunctorEquivalence_unitIso_inv_app_unop]
          rw [CategoryTheory.Functor.commShiftIso_hom_naturality]
          erw [Category.assoc, Iso.inv_hom_id_app_assoc]
          simp only [Pretriangulated.opShiftFunctorEquivalence, Iso.trans_inv,
            NatTrans.comp_app, unop_comp, Category.assoc]

        have q_commShift_of_localization
            {C D E : Type 1} [Category.{0} C] [Category.{1} D] [Category.{1} E]
            [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
            (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.CommShift ℤ]
            {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
            [NatTrans.CommShift (Functor.whiskerLeft L τ) ℤ] : NatTrans.CommShift τ ℤ := by
          constructor
          intro n
          apply Localization.natTrans_ext L W
          intro X
          change (F.commShiftIso n).hom.app (L.obj X) ≫ (τ.app (L.obj X))⟦n⟧' =
            τ.app ((L.obj X)⟦n⟧) ≫ (G.commShiftIso n).hom.app (L.obj X)
          apply (cancel_epi (F.map ((L.commShiftIso n).hom.app X))).mp
          have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) n X
          simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
            Category.assoc] at h
          change F.map ((L.commShiftIso n).hom.app X) ≫ (F.commShiftIso n).hom.app (L.obj X) ≫
              (τ.app (L.obj X))⟦n⟧' = τ.app (L.obj (X⟦n⟧)) ≫
              G.map ((L.commShiftIso n).hom.app X) ≫ (G.commShiftIso n).hom.app (L.obj X) at h
          rw [h]
          rw [← τ.naturality_assoc]
          rfl

        letI q_mapHC_commShift {C D : Type 1} [Category.{0} C] [Category.{0} D] [Abelian C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
            NatTrans.CommShift (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) ℤ := by
          constructor
          intro n
          ext K i
          simp

        let q_contraCochainIso {C E : Type 1} [Category.{0} C] [Category.{0} E] [Abelian C] [Abelian E] (F : C ⥤ C) (G : E ⥤ E) (D : Cᵒᵖ ⥤ E) [F.Additive] [G.Additive] [D.Additive] (e : F.op ⋙ D ≅ D ⋙ G) :
            (F |>.mapHomologicalComplex (ComplexShape.up ℤ)).op ⋙ ((CochainComplex.opEquivalence C).functor ⋙ (D.mapHomologicalComplex (ComplexShape.up ℤ))) ≅
              ((CochainComplex.opEquivalence C).functor ⋙ (D.mapHomologicalComplex (ComplexShape.up ℤ))) ⋙ (G |>.mapHomologicalComplex (ComplexShape.up ℤ)) :=
          NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents
            (fun i => (e).app (Opposite.op (K.unop.X (-i))))
            (by intro i j hij; exact ((e).hom.naturality
              (K.unop.d (-j) (-i)).op).symm)) (fun f => by
              apply HomologicalComplex.Hom.ext
              funext i
              exact (e).hom.naturality (f.unop.f (-i)).op)

        letI q_contraCochainCommShift {C E : Type 1} [Category.{0} C] [Category.{0} E] [Abelian C] [Abelian E] (F : C ⥤ C) (G : E ⥤ E) (D : Cᵒᵖ ⥤ E) [F.Additive] [G.Additive] [D.Additive] (e : F.op ⋙ D ≅ D ⋙ G) : NatTrans.CommShift (q_contraCochainIso F G D e).hom ℤ := by
          constructor
          intro n
          apply NatTrans.ext
          funext K
          apply HomologicalComplex.Hom.ext
          funext i
          simp only [NatTrans.comp_app, Functor.commShiftIso_comp_hom_app,
            Functor.whiskerRight_app, Functor.whiskerLeft_app, HomologicalComplex.comp_f,
            q_contraCochainIso, NatIso.ofComponents_hom_app, HomologicalComplex.Hom.isoOfComponents_hom_f]
          simp only [Functor.op_commShiftIso_hom_app _ K n (-n) (by omega)]
          dsimp [Pretriangulated.shiftFunctorOpIso, g_opCommShift,
            g_opShiftIso, Functor.commShiftIso,
            Functor.commShiftMapCochainComplex, Functor.mapCochainComplexShiftIso]
          simp only [NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
            HomologicalComplex.Hom.isoOfComponents_hom_f, HomologicalComplex.Hom.isoOfComponents_inv_f,
            Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_comp,
            HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
            g_opMap, Quiver.Hom.unop_op, unop_id,
            HomologicalComplex.id_f]
          repeat' first
            | erw [F.map_id]
            | erw [D.map_id]
            | erw [G.map_id]
            | erw [op_id]
            | erw [unop_id]
            | erw [HomologicalComplex.id_f]
            | erw [Category.id_comp]
            | erw [Category.comp_id]
          have hm (A : CochainComplex C ℤ) {a b : ℤ} (h : a = b) :
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A).XIsoOfEq h =
                F.mapIso (A.XIsoOfEq h) := by
            subst b
            apply Iso.ext
            simp [HomologicalComplex.XIsoOfEq]
            rfl
          have hc (A : (CochainComplex C ℤ)ᵒᵖ) (j : ℤ) :
              ((Functor.commShiftIso (CochainComplex.opEquivalence C).functor n).hom.app A).f j =
                (A.unop.XIsoOfEq (show -(j+n) = -j + -n by omega)).hom.op := rfl
          simp only [hc]
          erw [hm]
          exact e.hom.naturality (K.unop.XIsoOfEq (show -(i+n) = -i + -n by omega)).hom.op

        let Fs (t : ℤ) := GradedComodule.internalShift F2 Coalgebra.dualSteenrod t

        let Ft (t : ℤ) := GradedModule.internalShift F2 steenrod t

        let O := (CochainComplex.opEquivalence SourceComodule).functor

        let Dc := dualToLeftModule.mapHomologicalComplex (ComplexShape.up ℤ)

        let dualCochainShift (t : ℤ) :=
          q_contraCochainIso (Fs t) (Ft t) dualToLeftModule (r_shiftDualNatIso t)

        letI q_opCompCommShift001 {C D E : Type 1} [Category.{0} C] [Category.{0} D] [Category.{1} E]
            [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
            (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ] :
            NatTrans.CommShift (Functor.opComp F G).hom ℤ := by
          constructor
          intro n
          apply NatTrans.ext
          funext X
          simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
            Functor.opComp, Iso.refl_hom, NatTrans.id_app, Functor.commShiftIso_comp_hom_app]
          simp only [Functor.op_commShiftIso_hom_app _ X n (-n) (by omega),
            Functor.op_commShiftIso_hom_app G (F.op.obj X) n (-n) (by omega),
            Functor.commShiftIso_comp_inv_app, Functor.comp_map, Functor.map_comp,
            Functor.op_map, unop_comp, Quiver.Hom.unop_op, op_comp, Category.assoc]
          dsimp [Pretriangulated.shiftFunctorOpIso]
          repeat' first
            | erw [(shiftFunctor Eᵒᵖ n).map_id]
            | erw [F.map_id]
            | erw [G.map_id]
            | erw [op_id]
            | erw [unop_id]
            | erw [Category.id_comp]
            | erw [Category.comp_id]

        letI q_opCompCommShift011 {C D E : Type 1} [Category.{0} C] [Category.{1} D] [Category.{1} E]
            [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
            (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ] :
            NatTrans.CommShift (Functor.opComp F G).hom ℤ := by
          constructor
          intro n
          apply NatTrans.ext
          funext X
          simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
            Functor.opComp, Iso.refl_hom, NatTrans.id_app, Functor.commShiftIso_comp_hom_app]
          simp only [Functor.op_commShiftIso_hom_app _ X n (-n) (by omega),
            Functor.op_commShiftIso_hom_app G (F.op.obj X) n (-n) (by omega),
            Functor.commShiftIso_comp_inv_app, Functor.comp_map, Functor.map_comp,
            Functor.op_map, unop_comp, Quiver.Hom.unop_op, op_comp, Category.assoc]
          dsimp [Pretriangulated.shiftFunctorOpIso]
          repeat' first
            | erw [(shiftFunctor Eᵒᵖ n).map_id]
            | erw [F.map_id]
            | erw [G.map_id]
            | erw [op_id]
            | erw [unop_id]
            | erw [Category.id_comp]
            | erw [Category.comp_id]

        let Qs := DerivedCategory.Q (C := SourceComodule)

        let Qt := DerivedCategory.Q (C := LeftModule)

        let Lshift (t : ℤ) := (Fs t).mapDerivedCategory.op ⋙ dualDerived

        let Rshift (t : ℤ) := dualDerived ⋙ (Ft t).mapDerivedCategory

        let LshiftFactors (t : ℤ) :
            Qs.op ⋙ Lshift t ≅
              (((Fs t).mapHomologicalComplex (ComplexShape.up ℤ)).op ⋙ (O ⋙ Dc)) ⋙ Qt :=
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              ((Functor.opComp Qs (Fs t).mapDerivedCategory).symm ≪≫
                (NatIso.op (Fs t).mapDerivedCategoryFactors).symm ≪≫
                  Functor.opComp ((Fs t).mapHomologicalComplex (ComplexShape.up ℤ)) Qs) dualDerived ≪≫
              Functor.associator ((Fs t).mapHomologicalComplex (ComplexShape.up ℤ)).op Qs.op dualDerived ≪≫
                Functor.isoWhiskerLeft _ dualDerivedFactors ≪≫
                  Functor.isoWhiskerLeft _ ((Functor.associator O Dc Qt).symm) ≪≫
                    (Functor.associator _ _ _).symm

        let RshiftFactors (t : ℤ) :
            Qs.op ⋙ Rshift t ≅
              ((O ⋙ Dc) ⋙ (Ft t).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ Qt :=
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight dualDerivedFactors _ ≪≫
              Functor.isoWhiskerRight (Functor.associator O Dc Qt).symm _ ≪≫
                Functor.associator _ _ _ ≪≫
                  Functor.isoWhiskerLeft _ (Ft t).mapDerivedCategoryFactors ≪≫
                    (Functor.associator _ _ _).symm

        let derivedShiftPreIso (t : ℤ) : Qs.op ⋙ Lshift t ≅ Qs.op ⋙ Rshift t :=
          LshiftFactors t ≪≫ Functor.isoWhiskerRight (dualCochainShift t) Qt ≪≫
            (RshiftFactors t).symm

        let derivedShiftIso (t : ℤ) : Lshift t ≅ Rshift t :=
          Localization.liftNatIso Qs.op (HomologicalComplex.quasiIso SourceComodule (ComplexShape.up ℤ)).op
            (Qs.op ⋙ Lshift t) (Qs.op ⋙ Rshift t) (Lshift t) (Rshift t) (derivedShiftPreIso t)

        have derivedShiftIso_app (t : ℤ) (K : (CochainComplex SourceComodule ℤ)ᵒᵖ) :
            (derivedShiftIso t).hom.app (Qs.op.obj K) = (derivedShiftPreIso t).hom.app K := by
          simp [derivedShiftIso]

        letI LshiftFactors_commShift (t : ℤ) : NatTrans.CommShift (LshiftFactors t).hom ℤ := by
          simp only [LshiftFactors, Iso.trans_hom, Iso.symm_hom,
            Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatIso.op_inv]
          infer_instance

        letI RshiftFactors_commShift (t : ℤ) : NatTrans.CommShift (RshiftFactors t).hom ℤ := by
          simp only [RshiftFactors, Iso.trans_hom, Iso.symm_hom,
            Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
          infer_instance

        letI derivedShiftPreIso_commShift (t : ℤ) : NatTrans.CommShift (derivedShiftPreIso t).hom ℤ := by
          simp only [derivedShiftPreIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
          infer_instance

        letI derivedShiftIso_commShift (t : ℤ) : NatTrans.CommShift (derivedShiftIso t).hom ℤ := by
          have h : Functor.whiskerLeft Qs.op (derivedShiftIso t).hom = (derivedShiftPreIso t).hom := by
            apply NatTrans.ext
            funext K
            exact derivedShiftIso_app t K
          haveI : NatTrans.CommShift (Functor.whiskerLeft Qs.op (derivedShiftIso t).hom) ℤ := by
            rw [h]
            infer_instance
          exact q_commShift_of_localization Qs.op
            (HomologicalComplex.quasiIso SourceComodule (ComplexShape.up ℤ)).op (derivedShiftIso t).hom

        have singleTrivialIso_unique {Z : DerivedCategory LeftModule} (u : ℤ)
            (e f : Z ≅ (DerivedCategory.singleFunctor LeftModule 0).obj (trivialAt u)) : e = f := by
          let S := DerivedCategory.singleFunctor LeftModule 0
          let P := S.preimageIso (e.symm ≪≫ f)
          have hp : P = Iso.refl _ := r_trivialIso_unique u P (Iso.refl _)
          have hh := congrArg (fun i => S.map i.hom) hp
          change S.map (S.preimage (e.inv ≫ f.hom)) = S.map (𝟙 _) at hh
          rw [S.map_preimage, S.map_id] at hh
          apply Iso.ext
          apply (cancel_epi e.inv).mp
          rw [hh, e.inv_hom_id]

        let LshiftSingle (t : ℤ) (X : SourceComodule) :
            (Lshift t).obj (Opposite.op ((DerivedCategory.singleFunctor SourceComodule 0).obj X)) ≅
              (DerivedCategory.singleFunctor LeftModule 0).obj ((Ft t).obj (dualLeftModule X)) :=
          dualDerived.mapIso (((Fs t).mapDerivedCategorySingleFunctor 0).app X).symm.op ≪≫
            dualDerivedSingle ((Fs t).obj X) ≪≫
              (DerivedCategory.singleFunctor LeftModule 0).mapIso (r_shiftDualModuleIso X t)

        let RshiftSingle (t : ℤ) (X : SourceComodule) :
            (Rshift t).obj (Opposite.op ((DerivedCategory.singleFunctor SourceComodule 0).obj X)) ≅
              (DerivedCategory.singleFunctor LeftModule 0).obj ((Ft t).obj (dualLeftModule X)) :=
          (Ft t).mapDerivedCategory.mapIso (dualDerivedSingle X) ≪≫
            ((Ft t).mapDerivedCategorySingleFunctor 0).app (dualLeftModule X)

        have derivedShift_single_trivial (t u : ℤ) :
            (derivedShiftIso t).app (Opposite.op
                ((DerivedCategory.singleFunctor SourceComodule 0).obj (Ext.trivialAt u))) ≪≫
              RshiftSingle t (Ext.trivialAt u) = LshiftSingle t (Ext.trivialAt u) := by
          let N : (Ft t).obj (dualLeftModule (Ext.trivialAt u)) ≅ trivialAt (t+u) :=
            (Ft t).mapIso (trivialDualIso u) ≪≫
              KIP126.Algebra.GradedModule.internalShiftTrivialIso KIP126.Core.Algebra.F2 augmentation t u
          have h := singleTrivialIso_unique (t+u)
            (((derivedShiftIso t).app (Opposite.op
              ((DerivedCategory.singleFunctor SourceComodule 0).obj (Ext.trivialAt u))) ≪≫
              RshiftSingle t (Ext.trivialAt u)) ≪≫ (DerivedCategory.singleFunctor LeftModule 0).mapIso N)
            (LshiftSingle t (Ext.trivialAt u) ≪≫ (DerivedCategory.singleFunctor LeftModule 0).mapIso N)
          apply Iso.ext
          apply (cancel_mono ((DerivedCategory.singleFunctor LeftModule 0).map N.hom)).mp
          exact congrArg Iso.hom h

        have q_conjugate_map_eq {C D : Type 1} [Category.{1} C] [Category.{1} D]
            [HasShift C ℤ] [HasShift D ℤ]
            (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
            (e : F ≅ G) [NatTrans.CommShift e.hom ℤ]
            {X Y : C} {A B : D} {n : ℤ} (f : ShiftedHom X Y n)
            (lx : F.obj X ≅ A) (ly : F.obj Y ≅ B) (rx : G.obj X ≅ A) (ry : G.obj Y ≅ B)
            (hx : e.app X ≪≫ rx = lx) (hy : e.app Y ≪≫ ry = ly) :
            (ShiftedHom.mk₀ 0 rfl lx.inv).comp
              ((f.map F).comp (ShiftedHom.mk₀ 0 rfl ly.hom) (zero_add _)) (add_zero _) =
            (ShiftedHom.mk₀ 0 rfl rx.inv).comp
              ((f.map G).comp (ShiftedHom.mk₀ 0 rfl ry.hom) (zero_add _)) (add_zero _) := by
          rw [← hx, ← hy]
          have h := ShiftedHom.map_naturality_1 f e
          simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at h ⊢
          simp only [Iso.trans_inv, Iso.trans_hom, Functor.map_comp, Category.assoc]
          rw [← h]
          simp only [Category.assoc]
          rfl

        have dualExt_internalShift {u v : ℤ} {n : ℕ}
            (x : Abelian.Ext (Ext.trivialAt u) (Ext.trivialAt v) n) (t : ℤ) :
            (Abelian.Ext.mk₀ (r_shiftDualModuleIso (Ext.trivialAt v) t).inv).comp
              ((dualExt (x.mapExactFunctor (Fs t))).comp
                (Abelian.Ext.mk₀ (r_shiftDualModuleIso (Ext.trivialAt u) t).hom) (Nat.add_zero _)) (Nat.zero_add _) =
              (dualExt x).mapExactFunctor (Ft t) := by
          have hm : (x.mapExactFunctor (Fs t)).hom =
              (ShiftedHom.mk₀ 0 rfl (((Fs t).mapDerivedCategorySingleFunctor 0).inv.app (Ext.trivialAt u))).comp
                ((x.hom.map (Fs t).mapDerivedCategory).comp
                  (ShiftedHom.mk₀ 0 rfl (((Fs t).mapDerivedCategorySingleFunctor 0).hom.app (Ext.trivialAt v)))
                  (zero_add _)) (add_zero _) := by
            rw [Abelian.Ext.mapExactFunctor_hom]
            simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
          apply Abelian.Ext.ext
          simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom]
          rw [dualExt_hom, hm]
          rw [g_opEquiv_comp, g_opEquiv_comp] <;> try omega
          simp only [g_opEquiv_mk₀, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
          erw [opEquiv_map_derived]
          rw [Abelian.Ext.mapExactFunctor_hom, dualExt_hom]
          simp only [ShiftedHom.map_comp, ShiftedHom.map_mk₀]
          have h := q_conjugate_map_eq (Lshift t) (Rshift t) (derivedShiftIso t)
            (ShiftedHom.opEquiv (n:ℤ) x.hom)
            (LshiftSingle t (Ext.trivialAt v)) (LshiftSingle t (Ext.trivialAt u))
            (RshiftSingle t (Ext.trivialAt v)) (RshiftSingle t (Ext.trivialAt u))
            (derivedShift_single_trivial t v) (derivedShift_single_trivial t u)
          simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
            LshiftSingle, RshiftSingle, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
            Iso.op_hom, Iso.op_inv, Iso.symm_hom, Iso.symm_inv,
            Lshift, Rshift, ShiftedHom.comp_map, Functor.map_comp, Category.assoc] at h ⊢
          simp only [ShiftedHom.map, Functor.map_comp, Category.assoc] at h ⊢
          exact h

        let dualConjugate {X Y : SourceComodule} {X' Y' : LeftModule}
            (iX : dualLeftModule X ≅ X') (iY : dualLeftModule Y ≅ Y') {s : ℕ} (x : Abelian.Ext X Y s) :
            Abelian.Ext Y' X' s :=
          (Abelian.Ext.mk₀ iY.inv).comp ((dualExt x).comp (Abelian.Ext.mk₀ iX.hom) (Nat.add_zero _)) (Nat.zero_add _)

        have dualConjugate_comp {X Y Z : SourceComodule} {X' Y' Z' : LeftModule}
            (iX : dualLeftModule X ≅ X') (iY : dualLeftModule Y ≅ Y') (iZ : dualLeftModule Z ≅ Z')
            {a b c : ℕ} (x : Abelian.Ext X Y a) (y : Abelian.Ext Y Z b) (h : a+b=c) :
            dualConjugate iX iZ (x.comp y h) =
              (dualConjugate iY iZ y).comp (dualConjugate iX iY x) (by omega) := by
          simp only [dualConjugate, dualExt_comp]
          apply Abelian.Ext.ext
          simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
            ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
          simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
          simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
          rw [← NatTrans.naturality]
          simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
          erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

        have finishYoneda (R : Ext.CobarResolution)
            {e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
            (he : PreservesDualCobarRepresentatives R e)
            (hshift : ∀ (s : ℕ) (t u : ℤ) (y : Ext.SphereExt s u),
              dualConjugate (trivialDualIso (t+u)) (trivialDualIso t)
                (GradedComodule.coefficientShift Coalgebra.coaugmentation t s u y) =
              GradedModule.coefficientShift augmentation t s u (dualCoeff y)) : PreservesYoneda e := by
          intro s s' t t' x y
          simp only [comparison_eq_dualCoeff R he]
          change dualConjugate (trivialDualIso (t+t')) (trivialDualIso 0)
              ((GradedComodule.coefficientShift Coalgebra.coaugmentation t s' t' y).comp x (Nat.add_comm s' s)) =
            (dualConjugate (trivialDualIso t) (trivialDualIso 0) x).comp
              (GradedModule.coefficientShift augmentation t s' t' (dualCoeff y)) rfl
          rw [dualConjugate_comp (trivialDualIso (t+t')) (trivialDualIso t) (trivialDualIso 0), hshift]

        have dualCoefficientShift (s : ℕ) (t u : ℤ) (y : Ext.SphereExt s u)
            (hraw :
              (Abelian.Ext.mk₀ (r_shiftDualModuleIso (Ext.trivialAt 0) t).inv).comp
                ((dualExt (y.mapExactFunctor (Fs t))).comp
                  (Abelian.Ext.mk₀ (r_shiftDualModuleIso (Ext.trivialAt u) t).hom) (Nat.add_zero _)) (Nat.zero_add _) =
                (dualExt y).mapExactFunctor (Ft t)) :
            dualConjugate (trivialDualIso (t+u)) (trivialDualIso t)
              (GradedComodule.coefficientShift Coalgebra.coaugmentation t s u y) =
            GradedModule.coefficientShift augmentation t s u (dualCoeff y) := by
          let cS := GradedComodule.internalShiftTrivialIso F2 Coalgebra.coaugmentation t u
          let cT : (Fs t).obj (Ext.trivialAt 0) ≅ Ext.trivialAt t :=
            GradedComodule.internalShiftTrivialIso F2 Coalgebra.coaugmentation t 0 ≪≫ eqToIso (by rw [add_zero]; rfl)
          let mS : (Ft t).obj (trivialAt 0) ≅ trivialAt t :=
            GradedModule.internalShiftTrivialIso F2 augmentation t 0 ≪≫ eqToIso (by rw [add_zero]; rfl)
          let mT := GradedModule.internalShiftTrivialIso F2 augmentation t u
          have hS := r_trivialIso_unique (t+u)
            ((dualToLeftModule.mapIso cS.op).symm ≪≫ trivialDualIso (t+u))
            (r_shiftDualModuleIso (Ext.trivialAt u) t ≪≫
              (Ft t).mapIso (trivialDualIso u) ≪≫ mT)
          have hT := r_trivialIso_unique t
            ((dualToLeftModule.mapIso cT.op).symm ≪≫ trivialDualIso t)
            (r_shiftDualModuleIso (Ext.trivialAt 0) t ≪≫
              (Ft t).mapIso (trivialDualIso 0) ≪≫ mS)
          change (Abelian.Ext.mk₀ (trivialDualIso t).inv).comp
              ((dualExt (((Abelian.Ext.mk₀ cS.inv).comp (y.mapExactFunctor (Fs t)) (Nat.zero_add _)).comp
                (Abelian.Ext.mk₀ cT.hom) (Nat.add_zero _))).comp
                (Abelian.Ext.mk₀ (trivialDualIso (t+u)).hom) (Nat.add_zero _)) (Nat.zero_add _) =
            ((Abelian.Ext.mk₀ mS.inv).comp ((dualCoeff y).mapExactFunctor (Ft t)) (Nat.zero_add _)).comp
              (Abelian.Ext.mk₀ mT.hom) (Nat.add_zero _)
          simp only [dualExt_comp, dualExt_mk₀, dualCoeff, Abelian.Ext.mapExactFunctor_comp,
            Abelian.Ext.mapExactFunctor_mk₀]
          rw [← hraw]
          apply Abelian.Ext.ext
          simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
            ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
          have hhS := congrArg Iso.hom hS
          have hhT := congrArg Iso.inv hT
          simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv, Functor.mapIso_hom] at hhS
          simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Iso.op_hom, Functor.mapIso_inv] at hhT
          change dualLeftMap cS.inv ≫ (trivialDualIso (t+u)).hom =
            (r_shiftDualModuleIso (Ext.trivialAt u) t).hom ≫
              (Ft t).map (trivialDualIso u).hom ≫ mT.hom at hhS
          change (trivialDualIso t).inv ≫ dualLeftMap cT.hom =
            mS.inv ≫ (Ft t).map (trivialDualIso 0).inv ≫
              (r_shiftDualModuleIso (Ext.trivialAt 0) t).inv at hhT
          have hp := congrArg (fun f => (DerivedCategory.singleFunctor LeftModule 0).map f) hhT
          have hq := congrArg (fun f => (shiftFunctor (DerivedCategory LeftModule) (s : ℤ)).map
            ((DerivedCategory.singleFunctor LeftModule 0).map f)) hhS
          simp only [Functor.map_comp] at hp hq
          erw [reassoc_of% hp, hq]
          rfl
        apply finishYoneda R he
        intro s t u y
        exact dualCoefficientShift s t u y (dualExt_internalShift y t))

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- The same representative constraint also preserves the actual identity
class, with the same comparison family and source resolution. -/
theorem preservesUnit_of_preservesDualCobarRepresentatives (R : Ext.CobarResolution)
    {e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t}
    (he : PreservesDualCobarRepresentatives R e) : PreservesUnit e := by
  exact (open CategoryTheory KIP126.Algebra KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      classical
      let L := GradedComodule.degreeLine F2 0
      let E : L 0 ≅ ModuleCat.of F2 F2 := GradedObject.singleObjApplyIso 0 (ModuleCat.of F2 F2)
      have hj (f g : L ⟶ L) (h : CategoryStruct.comp E.inv (CategoryStruct.comp (f 0) E.hom) = CategoryStruct.comp E.inv (CategoryStruct.comp (g 0) E.hom)) : f = g := by
        funext n
        by_cases hn : n = 0
        · subst n
          exact (cancel_epi E.inv).mp ((cancel_mono E.hom).mp (by simpa only [Category.assoc] using h))
        · exact (GradedObject.isInitialSingleObjApply 0 (ModuleCat.of F2 F2) n hn).isZero.eq_of_src _ _
      have hends (f : L ⟶ L) : f = 0 ∨ f = CategoryStruct.id L := by
        let g := CategoryStruct.comp E.inv (CategoryStruct.comp (f 0) E.hom)
        have happ (x : F2) : g.hom x = x * g.hom 1 := by
          simpa only [smul_eq_mul,mul_one] using g.hom.map_smul x (1 : F2)
        have hc : ∀ c : F2, c = 0 ∨ c = 1 := by decide
        rcases hc (g.hom 1) with h | h
        · left
          apply hj
          have hg : g = 0 := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            change g.hom x = 0
            rw [happ,h,mul_zero]
          change g = CategoryStruct.comp E.inv (CategoryStruct.comp (0 : L 0 ⟶ L 0) E.hom)
          simpa only [Limits.comp_zero, Limits.zero_comp] using hg
        · right
          apply hj
          have hg : g = CategoryStruct.id (ModuleCat.of F2 F2) := by
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            change g.hom x = x
            rw [happ,h,mul_one]
          change g = CategoryStruct.comp E.inv (CategoryStruct.comp (CategoryStruct.id (L 0)) E.hom)
          simpa only [Category.id_comp, Iso.inv_hom_id] using hg
      have hid : (CategoryStruct.id L : L ⟶ L) ≠ 0 := by
        intro h
        have h' := congrArg (fun f : L ⟶ L => (CategoryStruct.comp E.inv (CategoryStruct.comp (f 0) E.hom)).hom (1 : F2)) h
        have hz : (1 : F2) = 0 := by simp at h'
        exact one_ne_zero hz
      have hu : Ext.unit ≠ 0 := by
        intro h
        have hz : (CategoryStruct.id (Ext.trivialAt 0) : Ext.trivialAt 0 ⟶ Ext.trivialAt 0) = 0 :=
          (Abelian.Ext.mk₀_eq_zero_iff _).mp h
        apply hid
        exact congrArg (fun f : Ext.trivialAt 0 ⟶ Ext.trivialAt 0 => f.f) hz
      have ht (x : SphereExt 0 0) : x = 0 ∨ x = unit := by
        obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective (trivialAt 0) (trivialAt 0)).surjective x
        rcases hends f.f with h | h
        · left
          have hf : f = 0 := Monad.Algebra.Hom.ext h
          simp [hf]
        · right
          have hf : f = CategoryStruct.id (trivialAt 0) := Monad.Algebra.Hom.ext h
          exact congrArg Abelian.Ext.mk₀ hf
      rcases ht (e 0 0 Ext.unit) with h | h
      · exact False.elim (hu ((e 0 0).injective (h.trans (map_zero (e 0 0)).symm)))
      · exact h)

end KIP126.Steenrod.Milnor.Module
