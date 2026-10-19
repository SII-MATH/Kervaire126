module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Data
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

def t1InclusionLocalizer : LocalizerMorphism t1StableEquivalences.{u} stableEquivalences :=
  LocalizerMorphism.ofEq rfl

noncomputable def cubicalT1Localizer :
    LocalizerMorphism stableEquivalences.{u} t1StableEquivalences where
  functor := cubicalT1Replacement
  map _ _ f hf := cubicalReplacementFunctor_map_stableEquivalence f hf

end KIP126.StableHomotopy.Implementation.Prespectrum
