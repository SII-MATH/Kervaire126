module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Sphere.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval

/-- Each original finite cube with a disjoint basepoint preserves
cubical cofibrations of the original compactly generated spectra. -/
theorem IsCubicalCofibration.spaceSmash_cube {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)]
    {f : X ⟶ Y} (hf : IsCubicalCofibration f) (n : ℕ) :
    IsCubicalCofibration (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeObject n))) f) := by
  induction n with
  | zero =>
    exact (spaceSmashMap_isCubicalCofibration_iff_of_iso
      BasedSpace.adjoinPointCubeZeroIso f).mpr
      (IsCubicalCofibration.spaceSmash_zeroSphere hf)
  | succ n ih =>
    apply (spaceSmashMap_isCubicalCofibration_iff_of_iso
      (BasedSpace.adjoinPointCubeSuccIso n) f).mpr
    exact (isCubicalCofibration_iff_of_iso
      (spaceSmashParameterProductIso (TopCat.of I) (cubeObject n) X)
      (spaceSmashParameterProductIso (TopCat.of I) (cubeObject n) Y) _ _
      (spaceSmashParameterProduct_natural (TopCat.of I) (cubeObject n) f)).mp
      (IsCubicalCofibration.spaceSmash_interval ih)

end KIP126.StableHomotopy.Implementation.Prespectrum
