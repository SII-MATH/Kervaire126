module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The original natural Moore unit respects the constructed coherent
integer shift comparisons. -/
instance sourceMooreCompletionNatUnit_commShift (p : ℕ) :
    (sourceMooreCompletionNatUnit.{u} p).CommShift ℤ where
  shift_comm d := by
    ext X
    change 𝟙 _ ≫ (sourceMooreCompletionUnit p X)⟦d⟧' =
      sourceMooreCompletionUnit p (X⟦d⟧) ≫ sourceMooreShiftComparison p d X
    rw [Category.id_comp]
    exact (sourceMooreShiftComparison_unit p d X).symm

end KIP126.StableHomotopy.Implementation

end
