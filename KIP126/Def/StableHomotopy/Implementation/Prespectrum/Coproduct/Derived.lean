module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Replacement.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- On the actual replacement of each summand, the displayed source
inclusion is exactly the localization of the original strict inclusion. -/
@[reassoc (attr := simp)]
theorem sourceDerivedSigmaCofan_inclusion_comparison {J : Type u}
    (X : J → SourceCategory.{u}) (j : J) :
    sourceLocalization.map (cubicalReplacementComparison.app (X j).as.obj) ≫
      (sourceDerivedSigmaCofan X).inj j =
        sourceLocalization.map (Sigma.ι (fun j => cubicalReplacementFunctor.obj (X j).as.obj) j) := by
  letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app (X j).as.obj)
    (cubicalReplacementComparison_stableEquivalence (X j).as.obj)
  dsimp only [sourceDerivedSigmaCofan, Cofan.inj, Cofan.mk_ι_app]
  simp

end KIP126.StableHomotopy.Implementation.Prespectrum

end
