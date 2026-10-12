module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceDesuspensionFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (desuspensionFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (desuspensionMap_stableEquivalence _ hf))

noncomputable def sourceTailFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (levelTailFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (levelTailMap_stableEquivalence _ hf))

noncomputable def sourceSuspensionFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (suspensionFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (suspensionMap_stableEquivalence _ hf))


end KIP126.StableHomotopy.Implementation.Prespectrum
