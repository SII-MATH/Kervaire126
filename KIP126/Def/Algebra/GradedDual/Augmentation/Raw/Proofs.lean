import KIP126.Def.Algebra.GradedDual.Augmentation.Raw.Data

/-! The prescribed evaluation preserves the convolution unit and product
because the specified coaugmentation is a comonoid morphism. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace
open scoped MonObj

universe u
variable {K : Type u} [Field K] {C : Comon (GrVect K)}

theorem convolutionAugmentation_unit (coaug : GradedComodule.Coaugmentation C) :
    η[(convolutionAlgebra C).X] ≫ convolutionAugmentationMap coaug = η[𝟙_ (GrVect K)] := by
  sorry

theorem convolutionAugmentation_mul (coaug : GradedComodule.Coaugmentation C) :
    μ[(convolutionAlgebra C).X] ≫ convolutionAugmentationMap coaug =
      (convolutionAugmentationMap coaug ⊗ₘ convolutionAugmentationMap coaug) ≫
        μ[𝟙_ (GrVect K)] := by
  sorry

end KIP126.Algebra.GradedDual
