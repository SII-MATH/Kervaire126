module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Integer.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Data
public import Mathlib.CategoryTheory.Shift.CommShift
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory

/-- The actual integer shifts of local spectra, with addition coherence
transported through the proved fully faithful inclusion into source spectra. -/
noncomputable instance hasShift : HasShift CompletedSpectrum ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful toSource).hasShift
    integerShiftFunctor toSource_integerShiftIso

/-- Inclusion preserves the coherent integer shifts, using the existing
comparison of the exact signed suspension iterates. -/
noncomputable instance toSource_commShift : toSource.CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful toSource) integerShiftFunctor toSource_integerShiftIso

end KIP126.StableHomotopy.Implementation.CompletedSpectrum

end

section

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

end
