module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Map.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval

/-- Smashing with the actual interval with a disjoint basepoint preserves
stable equivalences of the original compactly generated prespectra. -/
theorem spaceSmashMap_interval_stableEquivalence {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)]
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of I))) f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (mappingCylinderMap_stableEquivalence (𝟙 X) (𝟙 Y) f f (by simp) hf)
  haveI (Z : Prespectrum.{0}) [∀ n, UCompactlyGeneratedSpace.{0} (Z.level n)] :
      IsIso (sourceLocalization.map (spaceSmashIntervalComparison Z)) := by
    change IsIso (sourceLocalization.map (spaceSmashIntervalIso Z).hom)
    infer_instance
  have e := congrArg sourceLocalization.map (spaceSmashIntervalComparison_natural f)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
