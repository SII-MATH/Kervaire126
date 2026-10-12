module

public import KIP126.Def.CategoryTheory.Localization.Pi.Proofs

@[expose] public section

/- The discrete-diagram transport follows Joël Riou's finite-index proof in
Mathlib.CategoryTheory.Localization.Pi, with its finiteness step replaced by
the arbitrary-family right-fraction localization proved here. -/

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Functor

universe w u v u' v'

/-- Postcomposition by a localization with right fractions also localizes
arbitrary discrete diagrams at the pointwise equivalences. -/
theorem discrete_isLocalization_of_hasRightCalculus
    {J : Type w} {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (L : C ⥤ D) (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] [L.IsLocalization W] :
    ((whiskeringRight (Discrete J) C D).obj L).IsLocalization
      (W.functorCategory (Discrete J)) := by
  let E := piEquivalenceFunctorDiscrete J C
  let E' := piEquivalenceFunctorDiscrete J D
  let L₂ := (whiskeringRight (Discrete J) C D).obj L
  let L₁ := Functor.pi (fun (_ : J) => L)
  letI : L₁.IsLocalization (MorphismProperty.pi (fun _ => W)) :=
    pi_isLocalization_of_hasRightCalculus (fun (_ : J) => L) (fun _ => W)
  have : CatCommSq E.functor L₁ L₂ E'.functor :=
    ⟨(Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ E'.counitIso.symm ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (by exact Iso.refl _) _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight E.unitIso.symm L₁) _ ≪≫ isoWhiskerRight L₁.leftUnitor _⟩
  refine Functor.IsLocalization.of_equivalences L₁
    (MorphismProperty.pi (fun _ => W)) L₂ _ E E' ?_ ?_
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _ (fun ⟨j⟩ => hf j)
  · intro X Y f hf
    have : ∀ (j : Discrete J), IsIso ((L₂.map f).app j) :=
      fun j => Localization.inverts L W _ (hf j)
    apply NatIso.isIso_of_isIso_app

end KIP126.Foundation
