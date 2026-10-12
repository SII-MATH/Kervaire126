module

public import KIP126.Def.StableHomotopy.Implementation.Realization.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Opposite Simplicial

universe u

/-- The geometric realization of the actual singular simplicial set,
based at the vertex corresponding to the specified point. -/
noncomputable def singularRealization (A : BasedSpace.{u}) : BasedSpace.{u} :=
  basedRealization (TopCat.toSSet.obj A.space) (TopCat.toSSetObj₀Equiv.symm A.point)

/-- Evaluation of singular simplices is the actual realization--singular
adjunction counit. Its basedness and homotopy properties are separate claims. -/
noncomputable def singularEvaluation (A : BasedSpace.{u}) :
    C(singularRealization A, A) :=
  (sSetTopAdj.counit.app A.space).hom

end KIP126.StableHomotopy.Implementation
