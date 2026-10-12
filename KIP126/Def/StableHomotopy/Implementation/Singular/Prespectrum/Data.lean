module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Prespectrum.Bond.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
universe u

/-- The actual levelwise singular-realization prespectrum, with strict
bonds induced by the original structure maps and the simplicial interval. -/
noncomputable def singularPrespectrum (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := singularRealization (X.level n)
  bond := singularPrespectrumBond X
  bond_point := singularPrespectrumBond_point X
  bond_zero := singularPrespectrumBond_zero X
  bond_one := singularPrespectrumBond_one X

/-- Actual evaluation is a strict map of prespectra. -/
noncomputable def singularPrespectrumEvaluation (X : Prespectrum.{u}) :
    singularPrespectrum X ⟶ X where
  level n := singularEvaluation (X.level n)
  point n := singularEvaluation_point (X.level n)
  bond n := singularPrespectrumBond_evaluation X n

/-- Applying actual singular realization to a strict prespectrum map. -/
noncomputable def singularPrespectrumMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    singularPrespectrum X ⟶ singularPrespectrum Y where
  level n := singularRealizationMap (⟨f.level n,f.point n⟩ : X.level n ⟶ Y.level n)
  point n := singularRealizationMap_point _
  bond n := singularPrespectrumBond_natural f n

end KIP126.StableHomotopy.Implementation
