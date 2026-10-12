module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Functor

/-- Natural weak-equivalence counits in both directions exhibit an actual
equivalence after localization. -/
theorem isLocalizedEquivalence_of_counit_of_counit
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₁)
    (ε₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁)
    (ε₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂)
    (hε₁ : ∀ X, W₁ (ε₁.app X)) (hε₂ : ∀ X, W₂ (ε₂.app X)) :
    Φ.IsLocalizedEquivalence where
  isEquivalence := by
    have : IsIso (whiskerRight ε₁ W₁.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₁.Q W₁ _ (hε₁ _)
    have : IsIso (whiskerRight ε₂ W₂.Q) := by
      rw [NatTrans.isIso_iff_isIso_app]
      exact fun _ => Localization.inverts W₂.Q W₂ _ (hε₂ _)
    refine (Localization.equivalence W₁.Q W₁ W₂.Q W₂ (Φ.functor ⋙ W₂.Q)
      (Φ.localizedFunctor W₁.Q W₂.Q)
      (Ψ.functor ⋙ W₁.Q) (Ψ.localizedFunctor W₂.Q W₁.Q) ?_ ?_).isEquivalence_functor
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Ψ.functor W₂.Q W₁.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (whiskerRight ε₁ W₁.Q) ≪≫ Functor.leftUnitor _
    · exact Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (CatCommSq.iso Φ.functor W₁.Q W₂.Q _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        asIso (whiskerRight ε₂ W₂.Q) ≪≫ Functor.leftUnitor _

end KIP126.Foundation
