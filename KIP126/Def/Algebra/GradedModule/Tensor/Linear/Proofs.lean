import KIP126.Def.Algebra.GradedModule.Tensor.Data
import KIP126.Def.Algebra.GradedVectorSpace.Data
import KIP126.Def.Algebra.GradedVectorSpace.Proofs
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
Properties of the specified Cauchy left-tensor monad over a field. These are
conditions on its existing functor, not additional choices of functors.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (A : Mon (GrVect K))

theorem leftTensorMonad_additive :
    Functor.Additive (leftTensorMonad A : GrVect K ⥤ GrVect K) := by
  set_option backward.isDefEq.respectTransparency false in
    change (MonoidalCategory.tensorLeft A.X).Additive
    exact Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight A.X).symm

attribute [instance] leftTensorMonad_additive

theorem leftTensorMonad_linear :
    Functor.Linear K (leftTensorMonad A : GrVect K ⥤ GrVect K) := by
  set_option backward.isDefEq.respectTransparency false in
    change Functor.Linear K (MonoidalCategory.tensorLeft A.X)
    exact Functor.linear_of_iso K (BraidedCategory.tensorLeftIsoTensorRight A.X).symm

attribute [instance] leftTensorMonad_linear

/-- Cauchy tensoring on the left preserves finite colimits. -/
theorem leftTensorMonad_preservesFiniteColimits :
    PreservesFiniteColimits (leftTensorMonad A : GrVect K ⥤ GrVect K) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    have generalizedInverse {X Y : GrVect K} (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
      classical
      have hg (n : ℤ) : ∃ g : Y n ⟶ X n, f n ≫ g ≫ f n = f n := by
        obtain ⟨s, hs⟩ := (f n).hom.rangeRestrict.exists_rightInverse_of_surjective
          (f n).hom.range_rangeRestrict
        obtain ⟨r, hr⟩ := (LinearMap.range (f n).hom).subtype.exists_leftInverse_of_injective
          (Submodule.ker_subtype _)
        refine ⟨ModuleCat.ofHom (s.comp r), ?_⟩
        apply ModuleCat.hom_ext
        ext x
        have h₁ := LinearMap.congr_fun hr ((f n).hom.rangeRestrict x)
        have h₂ := congrArg Subtype.val (LinearMap.congr_fun hs ((f n).hom.rangeRestrict x))
        change (f n).hom (s (r ((f n).hom x))) = (f n).hom x
        rw [show r ((f n).hom x) = (f n).hom.rangeRestrict x from h₁]
        exact h₂
      choose g hg using hg
      exact ⟨g, funext hg⟩
    let F : GrVect K ⥤ GrVect K := leftTensorMonad A
    haveI : F.Additive := by
      change (MonoidalCategory.tensorLeft A.X).Additive
      exact Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight A.X).symm
    haveI (Y Z : GrVect K) (f : Y ⟶ Z) : PreservesColimit (parallelPair f 0) F := by
      obtain ⟨g, hg⟩ := generalizedInverse f
      have hp : f ≫ (𝟙 Z - g ≫ f) = 0 := by
        simp only [Preadditive.comp_sub, Category.comp_id, hg, sub_self]
      let s := cokernel.desc f (𝟙 Z - g ≫ f) hp
      have hqs : cokernel.π f ≫ s = 𝟙 Z - g ≫ f := cokernel.π_desc _ _ _
      have hsq : s ≫ cokernel.π f = 𝟙 (cokernel f) := by
        apply (cancel_epi (cokernel.π f)).1
        rw [← Category.assoc, hqs]
        simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
          cokernel.condition, comp_zero, sub_zero, Category.comp_id]
      apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
      refine (isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm ?_
      refine CokernelCofork.IsColimit.ofπ _ _ (fun h _ => F.map s ≫ h) ?_ ?_
      · intro W h hh
        rw [← Category.assoc, ← F.map_comp, hqs, F.map_sub, F.map_id,
          F.map_comp, Preadditive.sub_comp, Category.id_comp, Category.assoc,
          hh, comp_zero, sub_zero]
      · intro W h hh m hm
        rw [← hm, ← Category.assoc, ← F.map_comp, hsq, F.map_id, Category.id_comp]
    exact Functor.preservesFiniteColimits_of_preservesCokernels F

attribute [instance] leftTensorMonad_preservesFiniteColimits

end KIP126.Algebra.GradedModule
