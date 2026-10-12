module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Prespectrum.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
universe u

/-- The actual singular-realization endofunctor on strict prespectra. -/
noncomputable def singularPrespectrumFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj := singularPrespectrum
  map := singularPrespectrumMap
  map_id := singularPrespectrumMap_id
  map_comp := singularPrespectrumMap_comp

/-- Actual evaluation is a natural transformation to the identity functor. -/
noncomputable def singularPrespectrumEvaluationNatTrans :
    singularPrespectrumFunctor.{u} ⟶ 𝟭 Prespectrum.{u} where
  app := singularPrespectrumEvaluation
  naturality _ _ f := singularPrespectrumEvaluation_natural f

end KIP126.StableHomotopy.Implementation
