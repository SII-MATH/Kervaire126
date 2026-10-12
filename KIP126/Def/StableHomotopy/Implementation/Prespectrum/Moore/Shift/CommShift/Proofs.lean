module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.CommShift.Data

@[expose] public section

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
