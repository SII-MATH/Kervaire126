import KIP126.Def.Algebra.GradedModule.Shift.Data
import KIP126.Def.Algebra.GradedModule.Structure.Data

/-!
Linearity and exactness of the specified internal shift.  These properties
concern right tensoring by the actual degree line, whose opposite shift is
its inverse; they do not introduce an independently supplied exact functor.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (A : Mon (GrVect K)) (t : ℤ)

theorem internalShift_additive : (internalShift K A t).Additive := by
  sorry

attribute [instance] internalShift_additive

theorem internalShift_linear : Functor.Linear K (internalShift K A t) := by
  sorry

attribute [instance] internalShift_linear

theorem internalShift_preservesFiniteLimits :
    PreservesFiniteLimits (internalShift K A t) := by
  sorry

attribute [instance] internalShift_preservesFiniteLimits

theorem internalShift_preservesFiniteColimits :
    PreservesFiniteColimits (internalShift K A t) := by
  sorry

attribute [instance] internalShift_preservesFiniteColimits

end KIP126.Algebra.GradedModule
