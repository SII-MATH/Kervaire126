import KIP126.Def.Algebra.GradedModule.Structure.Basic.Proofs

/-!
The abelian structure uses the existing module category, linear operations,
created finite limits and colimits, and the coimage-image comparison property.
It is not a separately supplied background witness.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory GradedVectorSpace

universe u

variable {K : Type u} [Field K] (A : Mon (GrVect K))

noncomputable instance abelian : Abelian (LeftModule A) :=
  Abelian.ofCoimageImageComparisonIsIso

end KIP126.Algebra.GradedModule
