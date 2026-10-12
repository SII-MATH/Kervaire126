module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Preadditive.Data
public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Category.Data

@[expose] public section

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
