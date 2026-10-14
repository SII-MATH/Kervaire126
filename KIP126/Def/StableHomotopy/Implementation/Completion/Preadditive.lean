module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive
public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Category.Data

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

instance toSource_additive : toSource.Additive where
  map_add := rfl

instance hasFiniteBiproducts : HasFiniteBiproducts CompletedSpectrum :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance suspensionFunctor_additive : suspensionFunctor.Additive where
  map_add := Prespectrum.sourceSuspensionFunctor.map_add

instance desuspensionFunctor_additive : desuspensionFunctor.Additive where
  map_add := Prespectrum.sourceDesuspensionFunctor.map_add

end KIP126.StableHomotopy.Implementation.CompletedSpectrum

end
