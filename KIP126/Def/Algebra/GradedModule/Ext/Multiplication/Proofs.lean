import KIP126.Def.Algebra.GradedModule.Ext.Multiplication.Data

/-! The precise derived composition defining the left-module product. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory GradedVectorSpace

universe u

variable {K : Type u} [Field K] {A : Mon (GrVect K)}

/-- The formula records the left-module arrow order, distinct from the
right-comodule convention exchanged by contravariant dualization. -/
theorem coefficientYoneda_apply (ε : Augmentation A) (s s' : ℕ) (t u : ℤ)
    (x : CoefficientExt ε s t) (y : CoefficientExt ε s' u) :
    coefficientYoneda ε s s' t u x y =
      x.comp (coefficientShift ε t s' u y) rfl := rfl

end KIP126.Algebra.GradedModule
