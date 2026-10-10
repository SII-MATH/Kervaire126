import KIP126.Def.Algebra.GradedModule.Shift.TensorLine.Raw.Data

/-! Compatibility of scalar multiplication with the actual augmentation action. -/

namespace KIP126.Algebra.GradedModule.TensorLine

open CategoryTheory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

/-- The prescribed line multiplication intertwines the shifted trivial action
with the same augmentation action in the sum degree. -/
theorem iso_hom_action {A : Mon (GrVect K)} (ε : Augmentation A) (t u : ℤ) :
    (leftTensorMonad A).map (iso K t u).hom ≫ (trivialAt K ε (t + u)).a =
      ((internalShift K A t).obj (trivialAt K ε u)).a ≫ (iso K t u).hom := by
  sorry

end KIP126.Algebra.GradedModule.TensorLine
