module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Localization.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The existing source localization is also the localization of the actual
homotopy category at its descended stable equivalences. -/
instance homotopyToSource_isLocalization :
    homotopyToSource.{u}.IsLocalization homotopyStableEquivalences :=
  Functor.IsLocalization.mk' homotopyToSource homotopyStableEquivalences
    (homotopyToSourceUniversalProperty _)
    (homotopyToSourceUniversalProperty _)

end KIP126.StableHomotopy.Implementation.Prespectrum
