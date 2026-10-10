import KIP126.Def.Algebra.GradedDual.Raw.Data

/-! Associativity and unit properties of the prescribed convolution maps.
They use the same coalgebra's coassociativity and counitality; no algebra
operations or additional finite-dimensionality assumptions are supplied. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u
variable {K : Type u} [Field K] (C : Comon (GrVect K))

theorem convolutionUnit_mul :
    convolutionUnit C ▷ degreewiseDual C.X ≫ convolutionMultiplication C =
      (λ_ (degreewiseDual C.X)).hom := by
  sorry

theorem convolutionMul_unit :
    degreewiseDual C.X ◁ convolutionUnit C ≫ convolutionMultiplication C =
      (ρ_ (degreewiseDual C.X)).hom := by
  sorry

theorem convolutionMul_assoc :
    (convolutionMultiplication C ▷ degreewiseDual C.X) ≫ convolutionMultiplication C =
      (α_ (degreewiseDual C.X) (degreewiseDual C.X) (degreewiseDual C.X)).hom ≫
        (degreewiseDual C.X ◁ convolutionMultiplication C) ≫
          convolutionMultiplication C := by
  sorry

end KIP126.Algebra.GradedDual
