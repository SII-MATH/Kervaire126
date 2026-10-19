module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Cofibration.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval

/-- The actual interval tensor preserves cubical cofibrations on the
original compactly generated levels, through its strict cylinder comparison. -/
theorem IsCubicalCofibration.spaceSmash_interval {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)]
    {f : X ⟶ Y} (hf : IsCubicalCofibration f) :
    IsCubicalCofibration (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of I))) f) := by
  apply (isCubicalCofibration_iff_of_iso (spaceSmashIntervalIso X)
    (spaceSmashIntervalIso Y) _ (cylinderFunctor.map f)
    (spaceSmashIntervalComparison_natural f)).mpr
  exact IsCubicalCofibration.cylinder hf

end KIP126.StableHomotopy.Implementation.Prespectrum
