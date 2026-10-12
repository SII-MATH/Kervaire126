module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Suspension.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Suspension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The original zero-sphere smash preserves the actual lifting property
by the strict natural unit isomorphism. -/
theorem IsCubicalCofibration.spaceSmash_zeroSphere {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)]
    {f : X ⟶ Y} (hf : IsCubicalCofibration f) :
    IsCubicalCofibration (spaceSmashMap (𝟙 BasedSpace.zeroSphere) f) :=
  (isCubicalCofibration_iff_of_iso (spaceSmashUnitIso X) (spaceSmashUnitIso Y)
    _ f (spaceSmashUnit_natural f)).mpr hf

/-- Every original finite sphere parameter preserves cubical
cofibrations, by strict unit and suspension comparisons. -/
theorem IsCubicalCofibration.spaceSmash_sphere {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)]
    {f : X ⟶ Y} (hf : IsCubicalCofibration f) (n : ℕ) :
    IsCubicalCofibration (spaceSmashMap (𝟙 (sphereLevel n)) f) := by
  induction n with
  | zero => exact IsCubicalCofibration.spaceSmash_zeroSphere hf
  | succ n ih =>
    letI := (sphereLevel_good n).1
    intro E B p hp
    exact (isCubicalCofibration_iff_of_iso (spaceSmashSuspensionIso (sphereLevel n) X)
      (spaceSmashSuspensionIso (sphereLevel n) Y) _ _
      (spaceSmashSuspension_natural (sphereLevel n) f)).mpr
      (IsCubicalCofibration.suspension ih) p hp

end KIP126.StableHomotopy.Implementation.Prespectrum
