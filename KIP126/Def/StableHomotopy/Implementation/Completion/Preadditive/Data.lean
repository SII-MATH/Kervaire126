module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory

/-- Actual local spectra inherit the constructed ordinary-source addition
on their unchanged hom sets. -/
noncomputable instance preadditive : Preadditive CompletedSpectrum where
  homGroup A B := Prespectrum.sourcePreadditive.homGroup
    (sourceLocalization.obj A.spectrum) (sourceLocalization.obj B.spectrum)
  add_comp _ _ _ f g h := Preadditive.add_comp (C := SourceCategory.{0}) _ _ _ f g h
  comp_add _ _ _ f g h := Preadditive.comp_add (C := SourceCategory.{0}) _ _ _ f g h

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
