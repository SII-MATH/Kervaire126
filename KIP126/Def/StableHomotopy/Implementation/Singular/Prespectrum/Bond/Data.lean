module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Map

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Simplicial
open scoped unitInterval
universe u

/-- The original bond evaluated on actual singular representatives. -/
noncomputable def singularBondDomain (X : Prespectrum.{u}) (n : ℕ) :
    C(singularRealization (X.level n) × I, X.level (n+1)) :=
  (X.bond n).comp ((singularEvaluation (X.level n)).prodMap (ContinuousMap.id I))

/-- The actual singular-realization bond, using the realized simplicial interval. -/
noncomputable def singularPrespectrumBond (X : Prespectrum.{u}) (n : ℕ) :
    C(singularRealization (X.level n) × I, singularRealization (X.level (n+1))) :=
  singularCylinder (TopCat.toSSet.obj (X.level n).space) (X.level (n+1)).space
    (singularBondDomain X n)

end KIP126.StableHomotopy.Implementation
