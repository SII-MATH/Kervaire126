module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Chosen.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Restriction.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual degree-n Postnikov layer is the chosen fiber of the specified
restriction from cutoff n+1 to cutoff n. -/
noncomputable def sourcePostnikovLayer (X : SourceCategory.{0}) (n : ℤ) : SourceCategory :=
  sourceChosenFiber (sourcePostnikovRestriction X (n+1) n (by omega))

/-- The original fiber inclusion into the actual upper truncation. -/
noncomputable def sourcePostnikovLayerInclusion (X : SourceCategory.{0}) (n : ℤ) :
    sourcePostnikovLayer X n ⟶ sourcePostnikovTruncation X (n+1) :=
  sourceChosenFiberInclusion (sourcePostnikovRestriction X (n+1) n (by omega))

end KIP126.StableHomotopy.Implementation
