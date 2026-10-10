import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Monad.Algebra

/-! The prescribed unit and multiplication for left tensoring by a monoid. -/

namespace KIP126.Algebra.GradedModule.LeftTensor

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- Insert the actual monoid unit on the left of the given object. -/
def unitApp (A : Mon V) (X : V) : X ⟶ A.X ⊗ X :=
  (λ_ X).inv ≫ (η[A.X] ▷ X)

/-- Multiply the two left factors using the actual associator. -/
def mulApp (A : Mon V) (X : V) : A.X ⊗ (A.X ⊗ X) ⟶ A.X ⊗ X :=
  (α_ A.X A.X X).inv ≫ (μ[A.X] ▷ X)

end KIP126.Algebra.GradedModule.LeftTensor
