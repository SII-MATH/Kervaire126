module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Replacement.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- The original strict coproduct and its original injections, mapped
to the fixed stable localization. -/
noncomputable def sourceStrictSigmaCofan {J : Type u} (X : J → Prespectrum.{u}) :
    Cofan (fun j => sourceLocalization.obj (X j)) :=
  Cofan.mk (sourceLocalization.obj (∐ X)) (fun j => sourceLocalization.map (Sigma.ι X j))

end KIP126.StableHomotopy.Implementation.Prespectrum
