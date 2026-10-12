module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Integer.Coherence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Preadditive.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Additive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory KIP126.Foundation

/-- Every specified integer suspension iterate of actual local spectra is additive. -/
instance integerShiftFunctor_additive (d : ℤ) : (integerShiftFunctor d).Additive := by
  cases d <;> dsimp [integerShiftFunctor] <;> infer_instance

/-- All coherent local-spectrum shifts preserve addition on the original source hom sets. -/
instance shiftFunctor_additive (d : ℤ) : (shiftFunctor CompletedSpectrum d).Additive :=
  integerShiftFunctor_additive d

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
