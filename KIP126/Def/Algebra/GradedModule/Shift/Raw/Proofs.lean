import KIP126.Def.Algebra.GradedModule.Shift.Raw.Data

/-! Laws of the actual action on the shifted left module. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory GradedVectorSpace
open scoped MonObj

universe u

variable (K : Type u) [Field K]

theorem internalShiftAction_unit (A : Mon (GrVect K)) (t : ℤ) (M : LeftModule A) :
    (η[A.X] ▷ (M.A ⊗ GradedComodule.degreeLine K t)) ≫
        internalShiftAction K A t M =
      (λ_ (M.A ⊗ GradedComodule.degreeLine K t)).hom := by
  sorry

theorem internalShiftAction_assoc (A : Mon (GrVect K)) (t : ℤ) (M : LeftModule A) :
    (μ[A.X] ▷ (M.A ⊗ GradedComodule.degreeLine K t)) ≫
        internalShiftAction K A t M =
      (α_ A.X A.X (M.A ⊗ GradedComodule.degreeLine K t)).hom ≫
        (A.X ◁ internalShiftAction K A t M) ≫ internalShiftAction K A t M := by
  sorry

/-- Whiskering an actual left-module map by the degree line intertwines the
two prescribed shifted actions. -/
theorem internalShiftAction_map (A : Mon (GrVect K)) (t : ℤ)
    {M N : LeftModule A} (f : M ⟶ N) :
    (leftTensorMonad A).map (f.f ▷ GradedComodule.degreeLine K t) ≫
        internalShiftAction K A t N =
      internalShiftAction K A t M ≫ (f.f ▷ GradedComodule.degreeLine K t) := by
  sorry

end KIP126.Algebra.GradedModule
