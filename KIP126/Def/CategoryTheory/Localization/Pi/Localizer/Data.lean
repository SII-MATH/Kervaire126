module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.Pi.Basic

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

/-- The pointwise product of actual morphisms of localizers. -/
def piLocalizerMorphism {J : Type*} {C D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    {W : ∀ j, MorphismProperty (C j)} {W' : ∀ j, MorphismProperty (D j)}
    (Φ : ∀ j, LocalizerMorphism (W j) (W' j)) :
    LocalizerMorphism (MorphismProperty.pi W) (MorphismProperty.pi W') where
  functor := Functor.pi (fun j => (Φ j).functor)
  map _ _ f hf j := (Φ j).map (f j) (hf j)

end KIP126.Foundation
