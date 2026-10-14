module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Prespectrum.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
universe u

/-- Evaluation of the actual singular prespectrum is surjective on every
stable homotopy group. Injectivity is a further obligation. -/
theorem singularPrespectrumEvaluation_stableHomotopy_surjective
    (X : Prespectrum.{u}) (d : ℤ) :
    Function.Surjective (Prespectrum.stableHomotopyMap (singularPrespectrumEvaluation X) d) := by
  apply Prespectrum.stableHomotopyMap_surjective_of_levelHomotopy_surjective
  intro n r
  exact singularEvaluationHomotopy_surjective (X.level n) r

end KIP126.StableHomotopy.Implementation
