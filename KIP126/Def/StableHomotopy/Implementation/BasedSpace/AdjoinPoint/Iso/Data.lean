module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory
universe u

/-- An actual topological isomorphism extends by the identity on the
specified disjoint basepoint. -/
def adjoinPointIso {A B : TopCat.{u}} (e : A ≅ B) : adjoinPoint A ≅ adjoinPoint B where
  hom := adjoinPointMap e.hom
  inv := adjoinPointMap e.inv
  hom_inv_id := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro x
    cases x with
    | inl x => exact congrArg Sum.inl (congrArg (fun f : A ⟶ A => f x) e.hom_inv_id)
    | inr x => rfl
  inv_hom_id := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro x
    cases x with
    | inl x => exact congrArg Sum.inl (congrArg (fun f : B ⟶ B => f x) e.inv_hom_id)
    | inr x => rfl

end KIP126.StableHomotopy.Implementation.BasedSpace
