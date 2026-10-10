import KIP126.Def.Algebra.GradedVectorSpace.Data
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! Properties of the actual Cauchy tensor functor over a field. Its finite
limit preservation uses flatness of vector spaces and exactness of direct
sums. These are proof obligations on the fixed functor, not extra data. -/

namespace KIP126.Algebra.GradedVectorSpace

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u
variable {K : Type u} [Field K]

theorem tensorRight_additive (X : GrVect K) : (tensorRight X).Additive := by
  sorry

attribute [instance] tensorRight_additive

theorem tensorRight_linear (X : GrVect K) : Functor.Linear K (tensorRight X) := by
  sorry

attribute [instance] tensorRight_linear

/-- Degreewise Cauchy tensoring over a field preserves finite limits. -/
theorem tensorRight_preservesFiniteLimits (X : GrVect K) :
    PreservesFiniteLimits (tensorRight X) := by
  sorry

attribute [instance] tensorRight_preservesFiniteLimits

end KIP126.Algebra.GradedVectorSpace
