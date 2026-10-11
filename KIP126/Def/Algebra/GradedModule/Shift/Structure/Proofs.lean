module

public import KIP126.Def.Algebra.GradedModule.Shift.Data
public import KIP126.Def.Algebra.GradedModule.Structure.Data
public import KIP126.Def.Algebra.GradedVectorSpace.Proofs

@[expose] public section

/-!
Linearity and exactness of the specified internal shift.  These properties
concern right tensoring by the actual degree line, whose opposite shift is
its inverse; they do not introduce an independently supplied exact functor.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (A : Mon (GrVect K)) (t : ℤ)

theorem internalShift_additive : (internalShift K A t).Additive := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    intro M N f g
    apply Monad.Algebra.Hom.ext
    exact (MonoidalCategory.tensorRight (GradedComodule.degreeLine K t)).map_add (f := f.f) (g := g.f)

attribute [instance] internalShift_additive

theorem internalShift_linear : Functor.Linear K (internalShift K A t) := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    intro M N f r
    apply Monad.Algebra.Hom.ext
    exact (MonoidalCategory.tensorRight (GradedComodule.degreeLine K t)).map_smul r f.f

attribute [instance] internalShift_linear

theorem internalShift_preservesFiniteLimits :
    PreservesFiniteLimits (internalShift K A t) := by
  set_option backward.isDefEq.respectTransparency false in
    letI : PreservesFiniteLimits (forget A) :=
      inferInstanceAs (PreservesFiniteLimits (Monad.forget (leftTensorMonad A)))
    letI : ReflectsFiniteLimits (forget A) :=
      inferInstanceAs (ReflectsFiniteLimits (Monad.forget (leftTensorMonad A)))
    letI : PreservesFiniteLimits (MonoidalCategory.tensorRight (GradedComodule.degreeLine K t)) :=
      tensorRight_preservesFiniteLimits _
    letI : PreservesFiniteLimits (forget A ⋙ MonoidalCategory.tensorRight (GradedComodule.degreeLine K t)) :=
      comp_preservesFiniteLimits _ _
    let e : internalShift K A t ⋙ forget A ≅
        forget A ⋙ MonoidalCategory.tensorRight (GradedComodule.degreeLine K t) := Iso.refl _
    haveI : PreservesFiniteLimits (internalShift K A t ⋙ forget A) :=
      preservesFiniteLimits_of_natIso e.symm
    exact preservesFiniteLimits_of_reflects_of_preserves (internalShift K A t) (forget A)

attribute [instance] internalShift_preservesFiniteLimits

theorem internalShift_preservesFiniteColimits :
    PreservesFiniteColimits (internalShift K A t) := by
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
    have cauchyColimits (X : GrVect K) : PreservesFiniteColimits (MonoidalCategory.tensorRight X) := by
      classical
      let F := MonoidalCategory.tensorRight X
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
    letI : PreservesFiniteColimits (forget A) :=
      ⟨fun J _ _ => inferInstanceAs (PreservesColimitsOfShape J (Monad.forget (leftTensorMonad A)))⟩
    letI : ReflectsFiniteColimits (forget A) :=
      { reflects := fun J _ _ => inferInstanceAs (ReflectsColimitsOfShape J (Monad.forget (leftTensorMonad A))) }
    letI : PreservesFiniteColimits (MonoidalCategory.tensorRight (GradedComodule.degreeLine K t)) :=
      cauchyColimits _
    letI : PreservesFiniteColimits (forget A ⋙ MonoidalCategory.tensorRight (GradedComodule.degreeLine K t)) :=
      comp_preservesFiniteColimits _ _
    let e : internalShift K A t ⋙ forget A ≅
        forget A ⋙ MonoidalCategory.tensorRight (GradedComodule.degreeLine K t) := Iso.refl _
    haveI : PreservesFiniteColimits (internalShift K A t ⋙ forget A) :=
      preservesFiniteColimits_of_natIso e.symm
    exact preservesFiniteColimits_of_reflects_of_preserves (internalShift K A t) (forget A)

attribute [instance] internalShift_preservesFiniteColimits

end KIP126.Algebra.GradedModule
