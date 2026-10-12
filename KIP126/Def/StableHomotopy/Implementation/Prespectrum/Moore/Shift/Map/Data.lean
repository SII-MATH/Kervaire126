module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Orthogonality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The shift comparison extends the shifted actual Moore unit. -/
noncomputable def sourceMooreShiftComparison (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    sourceMooreCompletion p (X⟦d⟧) ⟶ (sourceMooreCompletion p X)⟦d⟧ :=
  ((sourceMooreCompletionUnit_precomp_bijective p (X⟦d⟧) _
    ((sourceMooreCompletion_scalarComplete p X).shift d)).surjective
    ((sourceMooreCompletionUnit p X)⟦d⟧')).choose

/-- The reverse comparison extends the unit of the shifted input, using
the proved universal property of the shifted original unit. -/
noncomputable def sourceMooreShiftComparisonInv (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    (sourceMooreCompletion p X)⟦d⟧ ⟶ sourceMooreCompletion p (X⟦d⟧) :=
  ((sourceMooreCompletionUnit_shift_precomp_bijective p X _ d
    (sourceMooreCompletion_scalarComplete p (X⟦d⟧))).surjective
    (sourceMooreCompletionUnit p (X⟦d⟧))).choose

end KIP126.StableHomotopy.Implementation
