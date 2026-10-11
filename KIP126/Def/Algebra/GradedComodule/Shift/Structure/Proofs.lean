module

public import KIP126.Def.Algebra.GradedComodule.Shift.Data
public import KIP126.Def.Algebra.GradedComodule.Structure.Data

@[expose] public section

/-!
Properties of the prescribed internal suspension, which tensors on the left
with the actual degree line. These assertions concern that fixed functor;
they do not supply another exact functor as a parameter. Its inverse is the
opposite internal suspension, so finite limits and colimits are preserved.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (C : Comon (GrVect K)) (t : ℤ)

theorem internalShift_additive : (internalShift K C t).Additive := by
  letI : (MonoidalCategory.tensorLeft (degreeLine K t)).Additive :=
    Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight (degreeLine K t)).symm
  constructor
  intro X Y f g
  apply Comonad.Coalgebra.Hom.ext
  exact Functor.map_add (MonoidalCategory.tensorLeft (degreeLine K t))

attribute [instance] internalShift_additive

theorem internalShift_linear : Functor.Linear K (internalShift K C t) := by
  letI : Functor.Linear K (MonoidalCategory.tensorLeft (degreeLine K t)) :=
    Functor.linear_of_iso K (BraidedCategory.tensorLeftIsoTensorRight (degreeLine K t)).symm
  constructor
  intro X Y f r
  apply Comonad.Coalgebra.Hom.ext
  exact Functor.map_smul (MonoidalCategory.tensorLeft (degreeLine K t)) r f.f

attribute [instance] internalShift_linear

theorem internalShift_preservesFiniteLimits :
    PreservesFiniteLimits (internalShift K C t) := by
  letI : PreservesFiniteLimits (MonoidalCategory.tensorLeft (degreeLine K t)) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (degreeLine K t)).symm
  letI : PreservesFiniteLimits (forget C) := ⟨fun _ _ _ => by unfold forget; infer_instance⟩
  letI : ReflectsFiniteLimits (forget C) := ⟨fun _ _ _ => by unfold forget; infer_instance⟩
  letI : PreservesFiniteLimits (internalShift K C t ⋙ forget C) := by
    exact comp_preservesFiniteLimits (forget C) (MonoidalCategory.tensorLeft (degreeLine K t))
  exact preservesFiniteLimits_of_reflects_of_preserves (internalShift K C t) (forget C)

attribute [instance] internalShift_preservesFiniteLimits

theorem internalShift_preservesFiniteColimits :
    PreservesFiniteColimits (internalShift K C t) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    letI : (MonoidalCategory.tensorLeft (degreeLine K t)).Additive :=
      Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight (degreeLine K t)).symm
    have hgInv {X Y : GrVect K} (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
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
    letI : PreservesFiniteColimits (MonoidalCategory.tensorLeft (degreeLine K t)) := by
      classical
      let F := MonoidalCategory.tensorLeft (degreeLine K t)
      haveI (Y Z : GrVect K) (f : Y ⟶ Z) : PreservesColimit (parallelPair f 0) F := by
        obtain ⟨g, hg⟩ := hgInv f
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
    letI : PreservesFiniteColimits (forget C) := by
      unfold forget
      infer_instance
    letI : ReflectsFiniteColimits (forget C) := by
      unfold forget
      infer_instance
    letI : PreservesFiniteColimits (internalShift K C t ⋙ forget C) := by
      exact comp_preservesFiniteColimits (forget C) (MonoidalCategory.tensorLeft (degreeLine K t))
    exact preservesFiniteColimits_of_reflects_of_preserves (internalShift K C t) (forget C)

attribute [instance] internalShift_preservesFiniteColimits

end KIP126.Algebra.GradedComodule
