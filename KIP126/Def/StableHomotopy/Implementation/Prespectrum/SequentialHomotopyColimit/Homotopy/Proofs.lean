module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- For every strict sequence, the stable homotopy groups of its actual
constructed telescope are the genuine colimits of the original stable
homotopy groups. No convergence or embedding assumption is supplied. -/
noncomputable def sequentialHomotopyStableCocone_isColimit
    (F : ℕ ⥤ Prespectrum.{u}) (d : ℤ) :
    IsColimit (sequentialHomotopyStableCocone F d) :=
  (IsColimit.precomposeInvEquiv (sequentialHomotopyStableComparison F d) _).symm
    (sequentialStableHomotopyCocone_isColimit (sequentialHomotopyDiagram F)
      (sequentialHomotopyDiagram_successor_closed F) d)

end KIP126.StableHomotopy.Implementation.Prespectrum
