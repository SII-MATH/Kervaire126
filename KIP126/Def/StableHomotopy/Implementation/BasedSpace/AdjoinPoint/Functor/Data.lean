module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Under.Data
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory
universe u

/-- The original disjoint-point construction as a functor, retaining
its actual sum topology and specified maps. -/
def adjoinPointFunctor : TopCat.{u} ⥤ BasedSpace.{u} where
  obj := adjoinPoint
  map := adjoinPointMap
  map_id A := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro x
    cases x <;> rfl
  map_comp f g := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro x
    cases x <;> rfl

/-- Adjoining the original disjoint point is left adjoint to forgetting
the specified point. -/
def adjoinPointAdjunction : adjoinPointFunctor.{u} ⊣ forgetToTop :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun A X => (adjoinPointEquiv A X).trans
      { toFun := TopCat.ofHom
        invFun := TopCat.Hom.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := by
      intro A B X f g
      apply Hom.ext
      apply ContinuousMap.ext
      intro x
      cases x <;> rfl
    homEquiv_naturality_right := by
      intro A X Y f g
      rfl }

end KIP126.StableHomotopy.Implementation.BasedSpace
