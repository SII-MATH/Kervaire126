import KIP126.Def.Steenrod.MilnorModule.Dualization.Raw.Data

/-! Precise properties of the prescribed transpose-conjugation action.
These statements do not assert an equivalence of unrestricted categories. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory MonoidalCategory KIP126.Algebra
open scoped MonObj

theorem conjugation_unit : η[steenrod.X] ≫ conjugation = η[steenrod.X] := by
  sorry

/-- Transposing anti-comultiplicativity reverses the convolution factors. -/
theorem conjugation_mul :
    μ[steenrod.X] ≫ conjugation =
      (conjugation ⊗ₘ conjugation) ≫ (β_ steenrod.X steenrod.X).hom ≫ μ[steenrod.X] := by
  sorry

theorem conjugation_involutive : conjugation ≫ conjugation = 𝟙 steenrod.X := by
  sorry

theorem dualLeftAction_unit (M : SourceComodule) :
    (η[steenrod.X] ▷ GradedDual.degreewiseDual M.A) ≫ dualLeftAction M =
      (λ_ (GradedDual.degreewiseDual M.A)).hom := by
  sorry

theorem dualLeftAction_assoc (M : SourceComodule) :
    (μ[steenrod.X] ▷ GradedDual.degreewiseDual M.A) ≫ dualLeftAction M =
      (α_ steenrod.X steenrod.X (GradedDual.degreewiseDual M.A)).hom ≫
        (steenrod.X ◁ dualLeftAction M) ≫ dualLeftAction M := by
  sorry

/-- A right-comodule map transposes to a left-module map in the opposite direction. -/
theorem dualLeftAction_naturality {M N : SourceComodule} (f : M ⟶ N) :
    (steenrod.X ◁ GradedDual.degreewiseDualMap f.f) ≫ dualLeftAction M =
      dualLeftAction N ≫ GradedDual.degreewiseDualMap f.f := by
  sorry

end KIP126.Steenrod.Milnor.Module
