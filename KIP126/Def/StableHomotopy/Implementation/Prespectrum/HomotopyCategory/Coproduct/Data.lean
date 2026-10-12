module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Quotient.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The original strict coproduct and inclusions, viewed in the quotient by
actual strict homotopy. -/
noncomputable def homotopyCoproductCofan {J : Type u} (X : J → Prespectrum.{u}) :
    Cofan (fun j => homotopyQuotient.obj (X j)) :=
  Cofan.mk (homotopyQuotient.obj (∐ X))
    (fun j => homotopyQuotient.map (Sigma.ι X j))

end KIP126.StableHomotopy.Implementation.Prespectrum
