module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Binary.Stability.General.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Smash.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Iso.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

/-- The actual endpoint tensor preserves stable equivalences for arbitrary
original spectra. Its compactly generated coproduct comparison is transported
through the actual zero-sphere unit, which becomes an isomorphism after smashing. -/
theorem spaceSmashMap_intervalBoundary_stableEquivalence_general
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint intervalBoundaryObject)) f) := by
  apply spaceSmashMap_stableEquivalence_of_compactlyGenerated _ ?_ f hf
  intro X Y hX hY f hf
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (coprodMap_stableEquivalence_general f f hf hf)
  haveI (Z : Prespectrum.{0}) [∀ n, UCompactlyGeneratedSpace.{0} (Z.level n)] :
      IsIso (sourceLocalization.map (spaceSmashIntervalBoundaryComparison Z)) := by
    change IsIso (sourceLocalization.map (spaceSmashIntervalBoundaryIso Z).hom)
    infer_instance
  have e := congrArg sourceLocalization.map (spaceSmashIntervalBoundaryComparison_natural f)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
