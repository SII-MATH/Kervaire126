import KIP126.Def.Algebra.GradedModule.Tensor.Data
import KIP126.Def.Algebra.GradedComodule.Shift.Data

/-!
# The actual left action on a right-tensored degree line

An internal shift tensors a left module on the right by the existing degree
line.  Only the original action and monoidal associator are used; no Hopf
structure or independently chosen action is required.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

/-- The specified left action on the underlying object of the internal shift. -/
noncomputable def internalShiftAction (A : Mon (GrVect K)) (t : ℤ)
    (M : LeftModule A) :
    A.X ⊗ (M.A ⊗ GradedComodule.degreeLine K t) ⟶
      M.A ⊗ GradedComodule.degreeLine K t :=
  (α_ A.X M.A (GradedComodule.degreeLine K t)).inv ≫
    (M.a ▷ GradedComodule.degreeLine K t)

end KIP126.Algebra.GradedModule
