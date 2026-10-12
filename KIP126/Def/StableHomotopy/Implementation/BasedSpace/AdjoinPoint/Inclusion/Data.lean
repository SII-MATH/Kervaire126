module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory

universe u

/-- The original summand inclusion into the actual disjoint-basepoint space. -/
def adjoinPointInclusion (A : TopCat.{u}) : A ⟶ (adjoinPoint A).space :=
  TopCat.ofHom ⟨Sum.inl,continuous_inl⟩

end KIP126.StableHomotopy.Implementation.BasedSpace
