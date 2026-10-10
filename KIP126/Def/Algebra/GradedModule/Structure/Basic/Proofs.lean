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
  sorry

attribute [instance] coimageImageComparison_isIso

end KIP126.Algebra.GradedModule
