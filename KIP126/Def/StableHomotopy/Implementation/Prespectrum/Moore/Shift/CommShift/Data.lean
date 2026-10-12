module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual additive Moore functor commutes coherently with all
integer shifts, by the zero and addition laws already proved. -/
noncomputable instance sourceMooreCompletionFunctor_commShift (p : ℕ) :
    (sourceMooreCompletionFunctor.{u} p).CommShift ℤ where
  commShiftIso := sourceMooreShiftNatIso p
  commShiftIso_zero := sourceMooreShiftNatIso_zero p
  commShiftIso_add := sourceMooreShiftNatIso_add p

end KIP126.StableHomotopy.Implementation
