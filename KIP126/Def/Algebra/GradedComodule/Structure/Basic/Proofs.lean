import KIP126.Def.Algebra.GradedComodule.Structure.Basic.Data
import Mathlib.CategoryTheory.Abelian.Basic

namespace KIP126.Algebra.GradedComodule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u
variable {K : Type u} [Field K] (C : Comon (GrVect K))

/-- The actual coimage-to-image comparison in graded right comodules is an
isomorphism. Both objects are constructed by the finite (co)limits created
by the forgetful functor. This is a property obligation, not chosen data. -/
theorem coimageImageComparison_isIso {X Y : RightComodule C} (f : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison f) := by
  sorry

attribute [instance] coimageImageComparison_isIso

end KIP126.Algebra.GradedComodule
