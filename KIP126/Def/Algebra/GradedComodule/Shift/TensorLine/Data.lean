import KIP126.Def.Algebra.GradedComodule.Shift.TensorLine.Raw.Proofs

/-!
The canonical tensor identification of degree lines and its lift to the
specified right-comodule category. Neither isomorphism is selected by choice:
both use the prescribed scalar multiplication and splitting maps.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

noncomputable section

/-- The canonical tensor identification, multiplying the scalar coordinates. -/
def degreeLineTensorIso (t u : ℤ) :
    degreeLine K t ⊗ degreeLine K u ≅ degreeLine K (t + u) where
  hom := TensorLine.hom K t u
  inv := TensorLine.inv K t u
  hom_inv_id := TensorLine.hom_inv_id K t u
  inv_hom_id := TensorLine.inv_hom_id K t u

/-- Tensoring the trivial comodule in degree `u` by the degree-`t` line gives
the same specified trivial coaction in degree `t + u`. -/
def internalShiftTrivialIso {C : Comon (GrVect K)} (η : Coaugmentation C) (t u : ℤ) :
    (internalShift K C t).obj (trivialAt K η u) ≅ trivialAt K η (t + u) :=
  Comonad.Coalgebra.isoMk (degreeLineTensorIso K t u) (TensorLine.hom_coaction K η t u)

end

end KIP126.Algebra.GradedComodule
