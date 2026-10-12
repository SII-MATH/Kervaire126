module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Derived.Data

@[expose] public section

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
