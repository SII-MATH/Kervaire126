import KIP126.Def.Algebra.GradedComodule.Shift.Data
import KIP126.Def.Algebra.GradedComodule.Structure.Data

/-!
Properties of the prescribed internal suspension, which tensors on the left
with the actual degree line. These assertions concern that fixed functor;
they do not supply another exact functor as a parameter. Its inverse is the
opposite internal suspension, so finite limits and colimits are preserved.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (C : Comon (GrVect K)) (t : ℤ)

theorem internalShift_additive : (internalShift K C t).Additive := by
  sorry

attribute [instance] internalShift_additive

theorem internalShift_linear : Functor.Linear K (internalShift K C t) := by
  sorry

attribute [instance] internalShift_linear

theorem internalShift_preservesFiniteLimits :
    PreservesFiniteLimits (internalShift K C t) := by
  sorry

attribute [instance] internalShift_preservesFiniteLimits

theorem internalShift_preservesFiniteColimits :
    PreservesFiniteColimits (internalShift K C t) := by
  sorry

attribute [instance] internalShift_preservesFiniteColimits

end KIP126.Algebra.GradedComodule
