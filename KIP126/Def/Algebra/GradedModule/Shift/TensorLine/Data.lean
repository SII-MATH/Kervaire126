import KIP126.Def.Algebra.GradedModule.Shift.TensorLine.Raw.Proofs

/-! The specified coefficient isomorphism in the actual left-module category. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

/-- Right tensoring the trivial degree-`u` module by the degree-`t` line gives
the same specified trivial module in degree `t+u`, through scalar multiplication. -/
noncomputable def internalShiftTrivialIso {A : Mon (GrVect K)}
    (ε : Augmentation A) (t u : ℤ) :
    (internalShift K A t).obj (trivialAt K ε u) ≅ trivialAt K ε (t + u) :=
  Monad.Algebra.isoMk (TensorLine.iso K t u) (TensorLine.iso_hom_action K ε t u)

end KIP126.Algebra.GradedModule
