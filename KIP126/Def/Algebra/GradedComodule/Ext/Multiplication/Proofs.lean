import KIP126.Def.Algebra.GradedComodule.Ext.Multiplication.Data

/-! The precise Ext composition underlying coefficient Yoneda multiplication. -/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory GradedVectorSpace

universe u

variable {K : Type u} [Field K] {C : Comon (GrVect K)}

/-- The second class is shifted by the internal degree of the first, and is
then composed with that first class in the actual derived Ext group. -/
theorem coefficientYoneda_apply (η : Coaugmentation C) (s s' : ℕ) (t u : ℤ)
    (x : CoefficientExt η s t) (y : CoefficientExt η s' u) :
    coefficientYoneda η s s' t u x y =
      (coefficientShift η t s' u y).comp x (Nat.add_comm s' s) := rfl

end KIP126.Algebra.GradedComodule
