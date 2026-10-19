module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The cocone on the original stable cubical quotients induced by the actual
sequential prespectrum inclusions. -/
noncomputable def sequentialStableHomotopyCocone (F : ℕ ⥤ Prespectrum.{u}) (d : ℤ) :
    Cocone (F ⋙ stableHomotopyFunctor d) :=
  (stableHomotopyFunctor d).mapCocone (sequentialColimitCocone F)

end KIP126.StableHomotopy.Implementation.Prespectrum
