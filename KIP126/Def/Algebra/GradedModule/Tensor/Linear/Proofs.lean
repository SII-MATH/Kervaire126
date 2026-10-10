import KIP126.Def.Algebra.GradedModule.Tensor.Data
import KIP126.Def.Algebra.GradedVectorSpace.Data
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
Properties of the specified Cauchy left-tensor monad over a field. These are
conditions on its existing functor, not additional choices of functors.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (A : Mon (GrVect K))

theorem leftTensorMonad_additive :
    Functor.Additive (leftTensorMonad A : GrVect K ⥤ GrVect K) := by
  sorry

attribute [instance] leftTensorMonad_additive

theorem leftTensorMonad_linear :
    Functor.Linear K (leftTensorMonad A : GrVect K ⥤ GrVect K) := by
  sorry

attribute [instance] leftTensorMonad_linear

/-- Cauchy tensoring on the left preserves finite colimits. -/
theorem leftTensorMonad_preservesFiniteColimits :
    PreservesFiniteColimits (leftTensorMonad A : GrVect K ⥤ GrVect K) := by
  sorry

attribute [instance] leftTensorMonad_preservesFiniteColimits

end KIP126.Algebra.GradedModule
