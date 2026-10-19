module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Cofiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The actual chosen cofiber of the upper sphere cover. -/
noncomputable def sourceUpperCellKilling (X : SourceCategory.{0}) (n : ℤ) : SourceCategory.{0} :=
  HasFunctorialCofiber.cofib (sourceUpperSphereCoverMap X n)

/-- The specified original cofiber inclusion. -/
noncomputable def sourceUpperCellKillingUnit (X : SourceCategory.{0}) (n : ℤ) :
    X ⟶ sourceUpperCellKilling X n :=
  HasFunctorialCofiber.cofibι (sourceUpperSphereCoverMap X n)

end KIP126.StableHomotopy.Implementation
