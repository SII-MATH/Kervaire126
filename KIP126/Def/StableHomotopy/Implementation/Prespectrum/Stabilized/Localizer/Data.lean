module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Category.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Separation.Localizer.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

def stabilizedInclusionLocalizer :
    LocalizerMorphism stabilizedStableEquivalences.{u} t1StableEquivalences :=
  LocalizerMorphism.ofEq rfl

noncomputable def stabilizedTelescopeLocalizer :
    LocalizerMorphism t1StableEquivalences.{u} stabilizedStableEquivalences where
  functor := stabilizedTelescope
  map _ _ f hf := spectrificationTelescopeMap_stableEquivalence f.hom hf

end KIP126.StableHomotopy.Implementation.Prespectrum
