module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Opposite Simplicial

universe u

/-- The actual vertex of singular realization corresponding to a point
of the original space. No continuity in the point parameter is asserted. -/
noncomputable def singularVertex (A : BasedSpace.{u}) (a : A) : singularRealization A :=
  (basedRealization (TopCat.toSSet.obj A.space) (TopCat.toSSetObj₀Equiv.symm a)).point

end KIP126.StableHomotopy.Implementation
