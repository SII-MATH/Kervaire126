import KIP126.Def.Algebra.GradedDual.Augmentation.Raw.Proofs

/-! The convolution augmentation is the actual evaluation map, bundled
with its separately stated algebra-morphism properties. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory GradedVectorSpace

universe u
variable {K : Type u} [Field K] {C : Comon (GrVect K)}

/-- The augmentation of the convolution algebra induced by the given
coaugmentation. In degree zero it sends `φ` to `φ(η(1))`. -/
noncomputable def convolutionAugmentation (η : GradedComodule.Coaugmentation C) :
    convolutionAlgebra C ⟶ Mon.trivial (GrVect K) :=
  Mon.Hom.mk' (convolutionAugmentationMap η)
    (convolutionAugmentation_unit η) (convolutionAugmentation_mul η)

end KIP126.Algebra.GradedDual
