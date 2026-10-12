module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Replacement.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual coproduct candidate in the original stable localization:
take the strict coproduct of the constructed free-cell replacements and
use the inverses of their proved stable-equivalence comparisons for the
inclusions. Its colimit property is a separate mathematical obligation. -/
noncomputable def sourceDerivedSigmaCofan {J : Type u} (X : J → SourceCategory.{u}) :
    Cofan X :=
  Cofan.mk
    (sourceLocalization.obj (∐ fun j => cubicalReplacementFunctor.obj (X j).as.obj))
    (fun j => by
      letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app (X j).as.obj)
        (cubicalReplacementComparison_stableEquivalence (X j).as.obj)
      exact inv (sourceLocalization.map (cubicalReplacementComparison.app (X j).as.obj)) ≫
        sourceLocalization.map (Sigma.ι (fun j => cubicalReplacementFunctor.obj (X j).as.obj) j))

end KIP126.StableHomotopy.Implementation.Prespectrum
