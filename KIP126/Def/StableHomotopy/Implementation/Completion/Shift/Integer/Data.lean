module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Category.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory KIP126.Foundation

/-- The exact signed iterate family of the proved local suspension
autoequivalence, before equipping it with an integer addition law. -/
noncomputable def integerShiftFunctor : ℤ → CompletedSpectrum ⥤ CompletedSpectrum
  | Int.ofNat n => functorIterate suspensionFunctor n
  | Int.negSucc n => functorIterate desuspensionFunctor (n + 1)

/-- Inclusion agrees strictly with every signed iterate, extending its
one-step compatibility to all integer degrees. -/
noncomputable def toSource_integerShiftIso (d : ℤ) :
    integerShiftFunctor d ⋙ toSource ≅ toSource ⋙ Prespectrum.sourceIntegerShiftFunctor d :=
  eqToIso (by
    cases d with
    | ofNat n =>
      exact functorIterate_comp suspensionFunctor
        Prespectrum.sourceSuspensionFunctor toSource rfl n
    | negSucc n =>
      exact functorIterate_comp desuspensionFunctor
        Prespectrum.sourceDesuspensionFunctor toSource rfl (n + 1))

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
