module

public import KIP126.Def.CategoryTheory.Localization.Fractions.Proofs
public import KIP126.Def.CategoryTheory.Localization.Pi.Fractions

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe w u v u' v'

set_option backward.isDefEq.respectTransparency false

/-- An arbitrary product of localizations is a localization when the
inverted classes admit right calculus of fractions. -/
theorem pi_isLocalization_of_hasRightCalculus
    {J : Type w} {C : J → Type u} {D : J → Type u'}
    [∀ j, Category.{v} (C j)] [∀ j, Category.{v'} (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).HasRightCalculusOfFractions] [∀ j, (L j).IsLocalization (W j)] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) := by
  letI : ∀ j, (L j).EssSurj := fun j => Localization.essSurj (L j) (W j)
  letI : (Functor.pi L).EssSurj :=
    { mem_essImage := fun Y =>
        ⟨fun j => (L j).objPreimage (Y j),
          ⟨{ hom := fun j => ((L j).objObjPreimageIso (Y j)).hom
             inv := fun j => ((L j).objObjPreimageIso (Y j)).inv
             hom_inv_id := funext (fun j => ((L j).objObjPreimageIso (Y j)).hom_inv_id)
             inv_hom_id := funext (fun j => ((L j).objObjPreimageIso (Y j)).inv_hom_id) }⟩⟩ }
  let hL := fun j => Localization.inverts (L j) (W j)
  apply isLocalization_of_rightFractions (MorphismProperty.pi W) (Functor.pi L)
    (MorphismProperty.IsInvertedBy.pi W L hL)
  · intro X Y f
    choose φ hφ using fun j => Localization.exists_rightFraction (L j) (W j) (f j)
    refine ⟨piRightFraction W φ, funext (fun j => ?_)⟩
    rw [rightFractionComponent_map W L hL]
    exact hφ j
  · intro X Y φ ψ h
    apply (pi_rightFractionRel_iff W φ ψ).mpr
    intro j
    have hj := congrFun h j
    rw [rightFractionComponent_map W L hL, rightFractionComponent_map W L hL] at hj
    exact (MorphismProperty.RightFraction.map_eq_iff (L j) (W j) _ _).mp hj

end KIP126.Foundation
