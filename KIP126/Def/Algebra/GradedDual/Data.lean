import KIP126.Def.Algebra.GradedDual.Raw.Proofs

/-! The actual graded convolution algebra of a graded coalgebra. Its
underlying maps were defined before the law statements; this bundle does
not choose a multiplication or require a dual-tensor isomorphism. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u
variable {K : Type u} [Field K]

/-- The same-degree graded linear dual with its actual convolution product.
The coproduct's two slots are not exchanged. The law proofs remain the
separate property obligations in `Raw/Proofs`. -/
noncomputable def convolutionAlgebra (C : Comon (GrVect K)) : Mon (GrVect K) where
  X := degreewiseDual C.X
  mon :=
    { one := convolutionUnit C
      mul := convolutionMultiplication C
      one_mul := convolutionUnit_mul C
      mul_one := convolutionMul_unit C
      mul_assoc := convolutionMul_assoc C }

end KIP126.Algebra.GradedDual
