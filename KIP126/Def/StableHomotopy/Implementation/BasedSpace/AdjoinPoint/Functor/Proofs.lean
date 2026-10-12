module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Functor.Data
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory CategoryTheory.Limits
universe u v w

@[simp] theorem adjoinPointMap_id (T : TopCat.{u}) :
    adjoinPointMap (𝟙 T) = 𝟙 (adjoinPoint T) :=
  adjoinPointFunctor.map_id T

@[simp] theorem adjoinPointMap_comp {T U V : TopCat.{u}}
    (f : T ⟶ U) (g : U ⟶ V) :
    adjoinPointMap (f ≫ g) = adjoinPointMap f ≫ adjoinPointMap g :=
  adjoinPointFunctor.map_comp f g

/-- Actual disjoint-point adjoining preserves colimits, with its original
sum construction and inclusions. -/
noncomputable instance adjoinPointFunctor_preservesColimits :
    PreservesColimitsOfSize.{v,w} adjoinPointFunctor.{u} :=
  adjoinPointAdjunction.leftAdjoint_preservesColimits

end KIP126.StableHomotopy.Implementation.BasedSpace
