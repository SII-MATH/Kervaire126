module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual pointwise loop functor on the original stable localization. -/
noncomputable def sourceLoopFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (loopFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (loopMap_stableEquivalence _ hf))

end KIP126.StableHomotopy.Implementation.Prespectrum
