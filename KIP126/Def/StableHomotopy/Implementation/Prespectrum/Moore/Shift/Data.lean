module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Map

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- Actual scalar completion commutes with each coherent integer shift. -/
noncomputable def sourceMooreShiftIso (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    sourceMooreCompletion p (X⟦d⟧) ≅ (sourceMooreCompletion p X)⟦d⟧ where
  hom := sourceMooreShiftComparison p d X
  inv := sourceMooreShiftComparisonInv p d X
  hom_inv_id := sourceMooreShiftComparison_hom_inv_id p d X
  inv_hom_id := sourceMooreShiftComparison_inv_hom_id p d X

/-- The objectwise comparison is natural on the original source category. -/
noncomputable def sourceMooreShiftNatIso (p : ℕ) (d : ℤ) :
    shiftFunctor SourceCategory.{u} d ⋙ sourceMooreCompletionFunctor p ≅
      sourceMooreCompletionFunctor p ⋙ shiftFunctor SourceCategory d :=
  NatIso.ofComponents (sourceMooreShiftIso p d)
    (fun f => sourceMooreShiftComparison_natural p d f)

end KIP126.StableHomotopy.Implementation
