module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Iso.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Iso.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Topology.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval

/-- The actual compact interval tensor retains the cubical lifting
property, via its original mapping-cylinder isomorphism. -/
theorem IsCubicallyCofibrant.spaceSmash_interval {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) :
    IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (TopCat.of I)) X) := by
  letI (n : ℕ) := hX.level_uCompactlyGeneratedSpace n
  intro E B p hp
  exact IsCubicallyCofibrant.of_iso (hX.mappingCylinder hX (𝟙 X))
    (spaceSmashIntervalIso X).symm p hp

/-- The actual first endpoint of the compact interval tensor is a
cubical cofibration when the original spectrum is cofibrant. -/
theorem spaceSmashIntervalAt_zero_isCubicalCofibration {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X)
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    IsCubicalCofibration (spaceSmashIntervalAt X 0) := by
  rw [← mappingCylinderInclusion_spaceSmashIntervalInverse X]
  apply IsCubicalCofibration.comp (mappingCylinderInclusion_isCubicalCofibration hX hX (𝟙 X))
  change IsCubicalCofibration (spaceSmashIntervalIso X).inv
  exact isCubicalCofibration_of_isIso _

/-- The actual other endpoint has the same proved lifting property. -/
theorem spaceSmashIntervalAt_one_isCubicalCofibration {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X)
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    IsCubicalCofibration (spaceSmashIntervalAt X 1) := by
  rw [← mappingCylinderSection_spaceSmashIntervalInverse X]
  apply IsCubicalCofibration.comp (mappingCylinderSection_isCubicalCofibration hX (𝟙 X))
  change IsCubicalCofibration (spaceSmashIntervalIso X).inv
  exact isCubicalCofibration_of_isIso _

end KIP126.StableHomotopy.Implementation.Prespectrum
