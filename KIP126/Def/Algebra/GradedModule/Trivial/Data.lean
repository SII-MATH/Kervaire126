import KIP126.Def.Algebra.GradedModule.Trivial.Raw.Proofs
import KIP126.Def.Algebra.GradedComodule.Shift.Data

/-! Actual trivial left modules on the existing integer-degree lines. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory GradedVectorSpace

universe u v

/-- The specified object with its actual action through the augmentation. -/
def trivialModule {V : Type u} [Category.{v} V] [MonoidalCategory V]
    {A : Mon V} (ε : Augmentation A) (X : V) : LeftModule A :=
  ofAction A X (trivialAction ε X) (trivialAction_unit ε X) (trivialAction_assoc ε X)

/-- The trivial left module concentrated in degree `t`. The underlying line
is the same one used for the right-comodule convention. -/
noncomputable def trivialAt (K : Type u) [Field K] {A : Mon (GrVect K)}
    (ε : Augmentation A) (t : ℤ) : LeftModule A :=
  trivialModule ε (GradedComodule.degreeLine K t)

end KIP126.Algebra.GradedModule
