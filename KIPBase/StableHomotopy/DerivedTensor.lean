import Mathlib.CategoryTheory.Localization.Bifunctor
import Mathlib.CategoryTheory.Functor.Currying
import KIPBase.StableHomotopy.StableModelCategory

/-!
# Derived tensor products

This file constructs the tensor bifunctor on the homotopy category of a
cofibrantly generated symmetric monoidal model category. Both inputs are
cofibrantly replaced before applying the point-set tensor product.
-/

universe v u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open MonoidalCategory MorphismProperty

namespace KIPBase.StableHomotopy

variable (C : Type u) [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasLimits C] [HasColimits C]
  [HasPushouts C] [HasInitial C] [SymMonoidalModelCategory C]
  [CofibrantlyGeneratedModelCategory C]

private noncomputable abbrev chosenCofibrantReplacement : C ⥤ C :=
  (inferInstance : CofibrantlyGeneratedModelCategory C).cofibrantReplacementFunctor

private noncomputable abbrev chosenCofibrantReplacementCounit :
    chosenCofibrantReplacement C ⟶ 𝟭 C :=
  (inferInstance : CofibrantlyGeneratedModelCategory C).cofibrantReplacementCounit

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasLimits C] [HasColimits C] [HasPushouts C] [HasInitial C]
  [SymMonoidalModelCategory C] in
/-- A functorial cofibrant replacement sends weak equivalences to weak
equivalences. -/
theorem chosenCofibrantReplacement_map_weakEquivalence {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) :
    weakEquivalences C ((chosenCofibrantReplacement C).map f) := by
  let G : CofibrantlyGeneratedModelCategory C := inferInstance
  have hX := CofibrantlyGeneratedModelCategory.cofibrantReplacementCounit_weakEquivalence
    C G X
  have hY := CofibrantlyGeneratedModelCategory.cofibrantReplacementCounit_weakEquivalence
    C G Y
  have hnat := (chosenCofibrantReplacementCounit C).naturality f
  haveI : WeakEquivalence ((chosenCofibrantReplacementCounit C).app Y) :=
    (weakEquivalence_iff _).2 hY
  haveI : WeakEquivalence
      ((chosenCofibrantReplacement C).map f ≫
        (chosenCofibrantReplacementCounit C).app Y) := by
    rw [hnat]
    exact (weakEquivalence_iff _).2
      ((weakEquivalences C).comp_mem _ _ hX hf)
  exact (weakEquivalence_iff _).1
    (weakEquivalence_of_postcomp
      ((chosenCofibrantReplacement C).map f)
      ((chosenCofibrantReplacementCounit C).app Y))

/-- The point-set bifunctor used to construct the derived tensor. Each input is
replaced by a cofibrant object before tensoring. -/
noncomputable def derivedTensorPreFunctor : C ⥤ C ⥤ Ho C :=
  Functor.curry.obj
    ((chosenCofibrantReplacement C).prod (chosenCofibrantReplacement C) ⋙
      Functor.uncurry.obj (curriedTensor C) ⋙ hoCat C)

private noncomputable def derivedTensorUncurried : C × C ⥤ Ho C :=
  (chosenCofibrantReplacement C).prod (chosenCofibrantReplacement C) ⋙
    Functor.uncurry.obj (curriedTensor C) ⋙ hoCat C

/-- This point-set bifunctor inverts weak equivalences in both variables.
The pushout-product axiom and Ken Brown's lemma apply because all four
replacement objects are cofibrant. -/
theorem derivedTensorPreFunctor_inverts :
    MorphismProperty.IsInvertedBy₂ (weakEquivalences C) (weakEquivalences C)
      (derivedTensorPreFunctor C) := by
  intro X Y f hf
  rcases X with ⟨X₁, X₂⟩
  rcases Y with ⟨Y₁, Y₂⟩
  rcases f with ⟨f₁, f₂⟩
  rcases hf with ⟨hf₁, hf₂⟩
  have hmap : IsIso ((hoCat C).map
      (((chosenCofibrantReplacement C).map f₁) ⊗ₘ
        ((chosenCofibrantReplacement C).map f₂))) := by
    let G : CofibrantlyGeneratedModelCategory C := inferInstance
    have h₁ := chosenCofibrantReplacement_map_weakEquivalence C f₁ hf₁
    have h₂ := chosenCofibrantReplacement_map_weakEquivalence C f₂ hf₂
    have hA₀ := CofibrantlyGeneratedModelCategory.cofibrantReplacement_isCofibrant
      C G X₁
    have hB₀ := CofibrantlyGeneratedModelCategory.cofibrantReplacement_isCofibrant
      C G Y₁
    have hX₀ := CofibrantlyGeneratedModelCategory.cofibrantReplacement_isCofibrant
      C G X₂
    have hY₀ := CofibrantlyGeneratedModelCategory.cofibrantReplacement_isCofibrant
      C G Y₂
    have hA : Cofibrant C ((chosenCofibrantReplacement C).obj X₁) :=
      ⟨(cofibration_iff _).1 hA₀⟩
    have hB : Cofibrant C ((chosenCofibrantReplacement C).obj Y₁) :=
      ⟨(cofibration_iff _).1 hB₀⟩
    have hX : Cofibrant C ((chosenCofibrantReplacement C).obj X₂) :=
      ⟨(cofibration_iff _).1 hX₀⟩
    have hY : Cofibrant C ((chosenCofibrantReplacement C).obj Y₂) :=
      ⟨(cofibration_iff _).1 hY₀⟩
    have ht := SymMonoidalModelCategory.tensorHom_weakEquivalence_of_cofibrant C
      ((chosenCofibrantReplacement C).map f₁)
      ((chosenCofibrantReplacement C).map f₂) h₁ h₂ hA hB hX hY
    exact Localization.inverts (hoCat C) (weakEquivalences C) _ ht
  have hraw : ((chosenCofibrantReplacement C).prod
      (chosenCofibrantReplacement C) ⋙ Functor.uncurry.obj (curriedTensor C)).map
      (f₁, f₂) =
      (((chosenCofibrantReplacement C).map f₁) ⊗ₘ
        ((chosenCofibrantReplacement C).map f₂)) := by
    change (Functor.uncurry.obj (curriedTensor C)).map
      (Prod.mkHom ((chosenCofibrantReplacement C).map f₁)
        ((chosenCofibrantReplacement C).map f₂)) = _
    simpa [Functor.uncurry, curriedTensor] using
      (tensorHom_def ((chosenCofibrantReplacement C).map f₁)
        ((chosenCofibrantReplacement C).map f₂)).symm
  have heq : (derivedTensorUncurried C).map (f₁, f₂) =
      (hoCat C).map
        (((chosenCofibrantReplacement C).map f₁) ⊗ₘ
          ((chosenCofibrantReplacement C).map f₂)) := by
    change (hoCat C).map
      (((chosenCofibrantReplacement C).prod (chosenCofibrantReplacement C) ⋙
        Functor.uncurry.obj (curriedTensor C)).map (f₁, f₂)) = _
    exact congrArg (hoCat C).map hraw
  have hpre : IsIso ((derivedTensorUncurried C).map (f₁, f₂)) := by
    rw [heq]
    exact hmap
  have huncurry : Functor.uncurry.obj (derivedTensorPreFunctor C) =
      derivedTensorUncurried C := by
    change Functor.uncurry.obj
      (Functor.curry.obj (derivedTensorUncurried C)) = derivedTensorUncurried C
    exact Functor.uncurry_obj_curry_obj _
  rw [huncurry]
  exact hpre

/-- The derived tensor bifunctor on `Ho C`. Its point-set definition uses
cofibrant replacement in each variable, so it requires no cofibrancy
assumption on the monoidal unit. -/
noncomputable def derivedTensorBifunctor : Ho C ⥤ Ho C ⥤ Ho C :=
  Localization.lift₂ (derivedTensorPreFunctor C)
    (derivedTensorPreFunctor_inverts C) (hoCat C) (hoCat C)

/-- Evaluating the derived tensor on objects coming from `C` is canonically
isomorphic to smashing their functorial cofibrant replacements. -/
noncomputable def derivedTensorBifunctor_compute (X Y : C) :
    ((derivedTensorBifunctor C).obj ((hoCat C).obj X)).obj ((hoCat C).obj Y) ≅
      (hoCat C).obj
        ((chosenCofibrantReplacement C).obj X ⊗
          (chosenCofibrantReplacement C).obj Y) := by
  let L := hoCat C
  let F := derivedTensorPreFunctor C
  let hF := derivedTensorPreFunctor_inverts C
  let F' := Localization.lift₂ F hF L L
  letI : Localization.Lifting₂ L L (weakEquivalences C) (weakEquivalences C)
      F F' := {
    iso := (Functor.curryObjProdComp _ _ _).symm ≪≫
      Functor.curry.mapIso (Localization.fac (Functor.uncurry.obj F) hF (L.prod L)) ≪≫
      Functor.currying.unitIso.symm.app F }
  let e := Localization.Lifting₂.iso L L (weakEquivalences C)
    (weakEquivalences C) F F'
  exact (e.app X).app Y

/-- On cofibrant inputs, the derived tensor agrees with the localization of the
ordinary point-set tensor. The comparison is the localized tensor of the two
cofibrant-replacement counits. -/
noncomputable def derivedTensorBifunctor_cofibrant_compute
    (X Y : C) (hX : Cofibrant C X) (hY : Cofibrant C Y) :
    ((derivedTensorBifunctor C).obj ((hoCat C).obj X)).obj ((hoCat C).obj Y) ≅
      (hoCat C).obj (X ⊗ Y) := by
  let G : CofibrantlyGeneratedModelCategory C := inferInstance
  let Q := chosenCofibrantReplacement C
  have hQX₀ := CofibrantlyGeneratedModelCategory.cofibrantReplacement_isCofibrant
    C G X
  have hQY₀ := CofibrantlyGeneratedModelCategory.cofibrantReplacement_isCofibrant
    C G Y
  have hQX : Cofibrant C (Q.obj X) := ⟨(cofibration_iff _).1 hQX₀⟩
  have hQY : Cofibrant C (Q.obj Y) := ⟨(cofibration_iff _).1 hQY₀⟩
  have hqX := CofibrantlyGeneratedModelCategory.cofibrantReplacementCounit_weakEquivalence
    C G X
  have hqY := CofibrantlyGeneratedModelCategory.cofibrantReplacementCounit_weakEquivalence
    C G Y
  have ht := SymMonoidalModelCategory.tensorHom_weakEquivalence_of_cofibrant C
    ((chosenCofibrantReplacementCounit C).app X)
    ((chosenCofibrantReplacementCounit C).app Y)
    hqX hqY hQX hX hQY hY
  let m : ((hoCat C).obj (Q.obj X ⊗ Q.obj Y)) ⟶ (hoCat C).obj (X ⊗ Y) := (hoCat C).map
    ((chosenCofibrantReplacementCounit C).app X ⊗ₘ
      (chosenCofibrantReplacementCounit C).app Y)
  letI : IsIso m := Localization.inverts (hoCat C) (weakEquivalences C) _ ht
  exact derivedTensorBifunctor_compute C X Y ≪≫ (asIso m)

end KIPBase.StableHomotopy
