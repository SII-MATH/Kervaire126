module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The constructed shift comparison has the required zero-shift coherence. -/
theorem sourceMooreShiftNatIso_zero (p : ℕ) :
    sourceMooreShiftNatIso.{u} p 0 = Functor.CommShift.isoZero
      (sourceMooreCompletionFunctor p) ℤ := by
  ext X
  apply (sourceMooreCompletionUnit_precomp_bijective p (X⟦(0 : ℤ)⟧) _
    ((sourceMooreCompletion_scalarComplete p X).shift 0)).injective
  simp only [Functor.CommShift.isoZero_hom_app]
  change sourceMooreCompletionUnit p (X⟦(0 : ℤ)⟧) ≫ sourceMooreShiftComparison p 0 X =
    sourceMooreCompletionUnit p (X⟦(0 : ℤ)⟧) ≫
      (sourceMooreCompletionMap p ((shiftFunctorZero SourceCategory ℤ).hom.app X) ≫
        (shiftFunctorZero SourceCategory ℤ).inv.app (sourceMooreCompletion p X))
  rw [sourceMooreShiftComparison_unit, ← Category.assoc, sourceMooreCompletionMap_unit]
  change (sourceMooreCompletionUnit p X)⟦(0 : ℤ)⟧' =
    ((shiftFunctorZero SourceCategory ℤ).hom.app X ≫ sourceMooreCompletionUnit p X) ≫
      (shiftFunctorZero SourceCategory ℤ).inv.app (sourceMooreCompletion p X)
  have h := (shiftFunctorZero SourceCategory ℤ).hom.naturality (sourceMooreCompletionUnit p X)
  change (sourceMooreCompletionUnit p X)⟦(0 : ℤ)⟧' ≫
    (shiftFunctorZero SourceCategory ℤ).hom.app (sourceMooreCompletion p X) =
      (shiftFunctorZero SourceCategory ℤ).hom.app X ≫ sourceMooreCompletionUnit p X at h
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The constructed shift comparisons respect addition of integers. -/
theorem sourceMooreShiftNatIso_add (p : ℕ) (a b : ℤ) :
    sourceMooreShiftNatIso.{u} p (a+b) = Functor.CommShift.isoAdd
      (sourceMooreShiftNatIso p a) (sourceMooreShiftNatIso p b) := by
  ext X
  apply (sourceMooreCompletionUnit_precomp_bijective p (X⟦a+b⟧) _
    ((sourceMooreCompletion_scalarComplete p X).shift (a+b))).injective
  simp only [Functor.CommShift.isoAdd_hom_app]
  change sourceMooreCompletionUnit p (X⟦a+b⟧) ≫ sourceMooreShiftComparison p (a+b) X =
    sourceMooreCompletionUnit p (X⟦a+b⟧) ≫
      (sourceMooreCompletionMap p ((shiftFunctorAdd SourceCategory a b).hom.app X) ≫
        sourceMooreShiftComparison p b (X⟦a⟧) ≫
          (sourceMooreShiftComparison p a X)⟦b⟧' ≫
            (shiftFunctorAdd SourceCategory a b).inv.app (sourceMooreCompletion p X))
  rw [sourceMooreShiftComparison_unit]
  rw [← Category.assoc, sourceMooreCompletionMap_unit]
  change (sourceMooreCompletionUnit p X)⟦a+b⟧' =
    ((shiftFunctorAdd SourceCategory a b).hom.app X ≫
      sourceMooreCompletionUnit p (X⟦a⟧⟦b⟧)) ≫
        (sourceMooreShiftComparison p b (X⟦a⟧) ≫
          (sourceMooreShiftComparison p a X)⟦b⟧' ≫
            (shiftFunctorAdd SourceCategory a b).inv.app (sourceMooreCompletion p X))
  simp only [Category.assoc]
  rw [← Category.assoc (sourceMooreCompletionUnit p (X⟦a⟧⟦b⟧)),
    sourceMooreShiftComparison_unit]
  rw [← CategoryTheory.Functor.map_comp_assoc, sourceMooreShiftComparison_unit]
  have h := (shiftFunctorAdd SourceCategory a b).hom.naturality (sourceMooreCompletionUnit p X)
  change (sourceMooreCompletionUnit p X)⟦a+b⟧' ≫
    (shiftFunctorAdd SourceCategory a b).hom.app (sourceMooreCompletion p X) =
      (shiftFunctorAdd SourceCategory a b).hom.app X ≫ (sourceMooreCompletionUnit p X)⟦a⟧'⟦b⟧' at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end KIP126.StableHomotopy.Implementation
