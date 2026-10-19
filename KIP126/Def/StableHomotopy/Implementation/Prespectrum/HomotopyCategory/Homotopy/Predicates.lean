module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data
public import Mathlib.CategoryTheory.Quotient

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Two strict maps are related exactly when an actual strict based path
homotopy exists between them. -/
def pathHomotopic : HomRel Prespectrum.{u} := fun _ _ f g => Nonempty (StrictHomotopy f g)

end KIP126.StableHomotopy.Implementation.Prespectrum
