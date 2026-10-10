import KIP126.Def.Algebra.GradedModule.Structure.Basic.Data
import Mathlib.CategoryTheory.Abelian.Basic

namespace KIP126.Algebra.GradedModule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

variable {K : Type u} [Field K] (A : Mon (GrVect K))

/-- The actual comparison built from the created kernel and cokernel objects
is an isomorphism. This is a property obligation on those fixed constructions. -/
theorem coimageImageComparison_isIso {X Y : LeftModule A} (f : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison f) := by
  let F := Monad.forget (leftTensorMonad A)
  letI : PreservesFiniteColimits F := ⟨fun J _ _ => inferInstance⟩
  haveI : IsIso (F.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso (Abelian.PreservesCoimageImageComparison.iso F f).hom]
    infer_instance
  exact isIso_of_reflects_iso (Abelian.coimageImageComparison f) F

attribute [instance] coimageImageComparison_isIso

end KIP126.Algebra.GradedModule
