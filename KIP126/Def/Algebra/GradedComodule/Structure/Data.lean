import KIP126.Def.Algebra.GradedComodule.Structure.Basic.Proofs

/-! The abelian structure on the fixed graded-comodule category is assembled
from its existing addition, created finite limits/colimits, and the stated
coimage-image isomorphism property. It is not a new interface parameter. -/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory GradedVectorSpace

universe u
variable {K : Type u} [Field K] (C : Comon (GrVect K))

noncomputable instance abelian : Abelian (RightComodule C) :=
  Abelian.ofCoimageImageComparisonIsIso

end KIP126.Algebra.GradedComodule
