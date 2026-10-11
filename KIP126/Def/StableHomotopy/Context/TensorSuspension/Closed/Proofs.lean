module

public import KIP126.Def.StableHomotopy.Context.TensorSuspension.Closed.Data
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

@[expose] public section


/-! Identify the ordinary mates with the same precomposition and currying.
These equalities do not assert compatibility with a chosen shift family. -/
namespace KIP126.StableHomotopy.TensorShift
open CategoryTheory MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- This mate is exactly Mathlib's objectwise currying operation. -/
theorem ihomTensorIso_hom_app (X Y B : C) :
    (ihomTensorIso X Y).hom.app B = MonoidalClosed.ihomCurry X Y B := by
  simp [ihomTensorIso, MonoidalClosed.ihomCurry, MonoidalClosed.curry_eq,
    Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]

variable [BraidedCategory C]

/-- The right mate is the original currying, preceded by the original braiding. -/
theorem rightIhomTensorIso_hom_app (X Y B : C) :
    (rightIhomTensorIso X Y).hom.app B =
      (MonoidalClosed.pre (β_ Y X).hom).app B ≫ MonoidalClosed.ihomCurry Y X B := by
  have h : (rightIhomTensorIso X Y).hom.app B =
      MonoidalClosed.curry ((β_ X ((ihom (X ⊗ Y)).obj B)).hom ≫
        MonoidalClosed.curry ((β_ Y (((ihom (X ⊗ Y)).obj B) ⊗ X)).hom ≫
          (α_ ((ihom (X ⊗ Y)).obj B) X Y).hom ≫
          (β_ (X ⊗ Y) ((ihom (X ⊗ Y)).obj B)).inv ≫
          (ihom.ev (X ⊗ Y)).app B)) := by
    calc
      _ = ((rightIhomAdjunction X).comp (rightIhomAdjunction Y)).homEquiv
          ((ihom (X ⊗ Y)).obj B) B
          ((α_ ((ihom (X ⊗ Y)).obj B) X Y).hom ≫
            (rightIhomAdjunction (X ⊗ Y)).counit.app B) := by
        simp only [rightIhomTensorIso, conjugateIsoEquiv_apply_hom,
          conjugateEquiv_apply_app, Adjunction.homEquiv_apply,
          Iso.symm_hom, tensorRightTensor_inv_app, Functor.map_comp]
      _ = _ := by
        rw [Adjunction.comp_homEquiv]
        change (rightIhomAdjunction X).homEquiv _ _
          ((rightIhomAdjunction Y).homEquiv _ _ _) = _
        simp only [rightIhomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
          MonoidalClosed.homEquiv_apply_eq]
        rfl

  rw [h]
  apply MonoidalClosed.uncurry_injective
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev,
    BraidedCategory.braiding_naturality_right_assoc]
  simp

/-- Naturality of the braiding identifies the ordinary right mate with precomposition. -/
theorem rightIhom_parameter_mate {X Y : C} (f : X ⟶ Y) :
    conjugateEquiv (rightIhomAdjunction Y) (rightIhomAdjunction X)
      ((tensoringRight C).map f) = MonoidalClosed.pre f := by
  ext B
  calc
    _ = (rightIhomAdjunction X).homEquiv _ B
        ((((tensoringRight C).map f).app ((ihom Y).obj B)) ≫
          (rightIhomAdjunction Y).counit.app B) := by
      simp only [conjugateEquiv_apply_app, Adjunction.homEquiv_apply,
        Functor.map_comp]
    _ = MonoidalClosed.curry ((f ▷ (ihom Y).obj B) ≫ (ihom.ev Y).app B) := by
      simp only [rightIhomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
        MonoidalClosed.homEquiv_apply_eq]
      congr 1
      change (β_ X ((ihom Y).obj B)).hom ≫
        (((ihom Y).obj B ◁ f) ≫ ((β_ Y ((ihom Y).obj B)).inv ≫
          (ihom.ev Y).app B)) = _
      rw [← BraidedCategory.braiding_naturality_left_assoc]
      simp
    _ = (MonoidalClosed.pre f).app B := by
      apply MonoidalClosed.uncurry_injective
      simp

/-- Equality of the full natural transformations, not merely a chosen component. -/
theorem rightIhomTensorIso_hom (X Y : C) :
    (rightIhomTensorIso X Y).hom =
      MonoidalClosed.pre (β_ Y X).hom ≫ (ihomTensorIso Y X).hom := by
  ext B
  simp only [NatTrans.comp_app, ihomTensorIso_hom_app, rightIhomTensorIso_hom_app]

end KIP126.StableHomotopy.TensorShift
