module

public import KIP126.Def.CategoryTheory.Functor.Iterate.Additive.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u

/-- Every specified integer suspension iterate preserves actual addition of source maps. -/
instance sourceIntegerShiftFunctor_additive (d : ℤ) :
    (sourceIntegerShiftFunctor.{u} d).Additive := by
  cases d <;> dsimp [sourceIntegerShiftFunctor] <;> infer_instance

/-- All coherent source shifts preserve the proved ordinary-source preadditive structure. -/
instance source_shiftFunctor_additive (d : ℤ) :
    (shiftFunctor SourceCategory.{u} d).Additive :=
  sourceIntegerShiftFunctor_additive d

end KIP126.StableHomotopy.Implementation.Prespectrum
