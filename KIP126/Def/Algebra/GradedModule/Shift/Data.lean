import KIP126.Def.Algebra.GradedModule.Shift.Raw.Proofs

/-! Internal shifts in the actual category of graded left modules. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u

variable (K : Type u) [Field K]

/-- A left module right-tensored by the actual degree-`t` line. -/
noncomputable def internalShiftObject (A : Mon (GrVect K)) (t : ℤ)
    (M : LeftModule A) : LeftModule A :=
  ofAction A (M.A ⊗ GradedComodule.degreeLine K t) (internalShiftAction K A t M)
    (internalShiftAction_unit K A t M) (internalShiftAction_assoc K A t M)

/-- The actual internal-degree shift functor.  Its action on objects and maps
is right tensoring by the degree line; it does not shift the Ext degree. -/
noncomputable def internalShift (A : Mon (GrVect K)) (t : ℤ) :
    LeftModule A ⥤ LeftModule A where
  obj M := internalShiftObject K A t M
  map f := ⟨f.f ▷ GradedComodule.degreeLine K t, internalShiftAction_map K A t f⟩
  map_id M := Monad.Algebra.Hom.ext ((tensorRight (GradedComodule.degreeLine K t)).map_id M.A)
  map_comp f g := Monad.Algebra.Hom.ext
    ((tensorRight (GradedComodule.degreeLine K t)).map_comp f.f g.f)

end KIP126.Algebra.GradedModule
