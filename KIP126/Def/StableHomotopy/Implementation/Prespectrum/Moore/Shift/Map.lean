module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Orthogonality.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

theorem sourceMooreShiftComparison_unit (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    sourceMooreCompletionUnit p (X⟦d⟧) ≫ sourceMooreShiftComparison p d X =
      (sourceMooreCompletionUnit p X)⟦d⟧' :=
  ((sourceMooreCompletionUnit_precomp_bijective p (X⟦d⟧) _
    ((sourceMooreCompletion_scalarComplete p X).shift d)).surjective
    ((sourceMooreCompletionUnit p X)⟦d⟧')).choose_spec

theorem sourceMooreShiftComparisonInv_unit (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    (sourceMooreCompletionUnit p X)⟦d⟧' ≫ sourceMooreShiftComparisonInv p d X =
      sourceMooreCompletionUnit p (X⟦d⟧) :=
  ((sourceMooreCompletionUnit_shift_precomp_bijective p X _ d
    (sourceMooreCompletion_scalarComplete p (X⟦d⟧))).surjective
    (sourceMooreCompletionUnit p (X⟦d⟧))).choose_spec

theorem sourceMooreShiftComparison_hom_inv_id (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    sourceMooreShiftComparison p d X ≫ sourceMooreShiftComparisonInv p d X = 𝟙 _ := by
  apply sourceMooreCompletion_hom_ext p
  rw [← Category.assoc, sourceMooreShiftComparison_unit,
    sourceMooreShiftComparisonInv_unit, Category.comp_id]

theorem sourceMooreShiftComparison_inv_hom_id (p : ℕ) (d : ℤ) (X : SourceCategory.{u}) :
    sourceMooreShiftComparisonInv p d X ≫ sourceMooreShiftComparison p d X = 𝟙 _ := by
  apply (sourceMooreCompletionUnit_shift_precomp_bijective p X _ d
    ((sourceMooreCompletion_scalarComplete p X).shift d)).injective
  change (sourceMooreCompletionUnit p X)⟦d⟧' ≫
    (sourceMooreShiftComparisonInv p d X ≫ sourceMooreShiftComparison p d X) =
      (sourceMooreCompletionUnit p X)⟦d⟧' ≫ 𝟙 _
  rw [← Category.assoc, sourceMooreShiftComparisonInv_unit,
    sourceMooreShiftComparison_unit, Category.comp_id]

/-- The actual comparison is natural for every localized source morphism. -/
theorem sourceMooreShiftComparison_natural (p : ℕ) (d : ℤ)
    {X Y : SourceCategory.{u}} (f : X ⟶ Y) :
    sourceMooreCompletionMap p (f⟦d⟧') ≫ sourceMooreShiftComparison p d Y =
      sourceMooreShiftComparison p d X ≫ (sourceMooreCompletionMap p f)⟦d⟧' := by
  apply (sourceMooreCompletionUnit_precomp_bijective p (X⟦d⟧) _
    ((sourceMooreCompletion_scalarComplete p Y).shift d)).injective
  change sourceMooreCompletionUnit p (X⟦d⟧) ≫
    (sourceMooreCompletionMap p (f⟦d⟧') ≫ sourceMooreShiftComparison p d Y) =
      sourceMooreCompletionUnit p (X⟦d⟧) ≫
        (sourceMooreShiftComparison p d X ≫ (sourceMooreCompletionMap p f)⟦d⟧')
  rw [← Category.assoc, sourceMooreCompletionMap_unit]
  rw [Category.assoc, sourceMooreShiftComparison_unit]
  rw [← Category.assoc, sourceMooreShiftComparison_unit]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    sourceMooreCompletionMap_unit]

end KIP126.StableHomotopy.Implementation

end
