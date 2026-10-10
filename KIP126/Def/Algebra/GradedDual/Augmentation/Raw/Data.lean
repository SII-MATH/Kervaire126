import KIP126.Def.Algebra.GradedDual.Data
import KIP126.Def.Algebra.GradedComodule.Tensor.Raw.Data

/-! Evaluation at a specified coaugmentation gives the actual augmentation
of the same-degree convolution algebra. No choice of character is made. -/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u
variable {K : Type u} [Field K] {C : Comon (GrVect K)}

noncomputable section

/-- The specified coaugmentation's value on the scalar `1`, in degree zero. -/
def coaugmentationElement (η : GradedComodule.Coaugmentation C) : C.X 0 :=
  (η.hom 0).hom
    ((show ModuleCat.of K K ⟶ (𝟙_ (GrVect K)) 0 from
      GradedObject.Monoidal.tensorUnit₀.inv).hom (1 : K))

/-- Evaluate degree-zero functionals on the specified coaugmentation and
use the zero map in every other degree. -/
def convolutionAugmentationMap (η : GradedComodule.Coaugmentation C) :
    (convolutionAlgebra C).X ⟶ 𝟙_ (GrVect K) := by
  classical
  intro n
  by_cases h : n = 0
  · subst n
    exact ModuleCat.ofHom (Module.Dual.eval K (C.X 0) (coaugmentationElement η)) ≫
      GradedObject.Monoidal.tensorUnit₀.inv
  · exact 0

end
end KIP126.Algebra.GradedDual
