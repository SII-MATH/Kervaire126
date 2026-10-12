module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Integer.Coherence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory

/-- The coherent local-spectrum shift is the exact signed iterate already constructed. -/
@[simp] theorem shiftFunctor_eq (d : ℤ) :
    shiftFunctor CompletedSpectrum d = integerShiftFunctor d := rfl

@[simp] theorem shiftFunctor_one :
    shiftFunctor CompletedSpectrum (1 : ℤ) = suspensionFunctor := rfl

@[simp] theorem shiftFunctor_neg_one :
    shiftFunctor CompletedSpectrum (-1 : ℤ) = desuspensionFunctor := rfl

/-- Coherent shift preservation by inclusion has exactly the previously
proved comparison on actual source objects and maps. -/
theorem toSource_commShiftIso_eq (d : ℤ) :
    toSource.commShiftIso d = toSource_integerShiftIso d := rfl

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
