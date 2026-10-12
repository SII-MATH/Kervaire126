module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Integer.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Data
public import Mathlib.CategoryTheory.Shift.CommShift

@[expose] public section

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
