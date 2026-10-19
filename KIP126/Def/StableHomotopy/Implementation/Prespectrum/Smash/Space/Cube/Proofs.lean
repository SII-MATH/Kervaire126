module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.CompactlyGenerated.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval

/-- Every original cubical cell parameter with a disjoint basepoint
preserves actual cubical cofibrancy of spectra. -/
theorem IsCubicallyCofibrant.spaceSmash_cube {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) :
    IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (cubeObject n)) X) := by
  induction n with
  | zero =>
    intro E B p hp
    exact IsCubicallyCofibrant.of_iso (hX.spaceSmash_sphere 0)
      (spaceSmashIso BasedSpace.adjoinPointCubeZeroIso (Iso.refl X)).symm p hp
  | succ n ih =>
    intro E B p hp
    exact IsCubicallyCofibrant.of_iso (IsCubicallyCofibrant.spaceSmash_interval ih)
      (spaceSmashCubeSuccIso n X).symm p hp

/-- Every original cubical cell parameter preserves the original stable
equivalences. The intermediate smash levels are actually compactly
generated; no compact-generation premise is imposed on the input spectra. -/
theorem spaceSmashMap_cube_stableEquivalence (n : ℕ) {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeObject n))) f) := by
  induction n with
  | zero =>
    exact (spaceSmashMap_stableEquivalence_iff_of_iso BasedSpace.adjoinPointCubeZeroIso f).mpr
      (spaceSmashMap_zeroSphere_stableEquivalence f hf)
  | succ n ih =>
    apply (spaceSmashMap_stableEquivalence_iff_of_iso (BasedSpace.adjoinPointCubeSuccIso n) f).mpr
    apply (stableEquivalence_iff_source_isIso _).mpr
    letI := stableEquivalences.Q_inverts _
      (spaceSmashMap_interval_stableEquivalence
        (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (cubeObject n))) f) ih)
    haveI (Z : Prespectrum.{0}) :
        IsIso (sourceLocalization.map (spaceSmashParameterProduct (TopCat.of I) (cubeObject n) Z)) := by
      change IsIso (sourceLocalization.map (spaceSmashParameterProductIso
        (TopCat.of I) (cubeObject n) Z).hom)
      infer_instance
    have e := congrArg sourceLocalization.map
      (spaceSmashParameterProduct_natural (TopCat.of I) (cubeObject n) f)
    simp only [Functor.map_comp] at e
    exact IsIso.of_isIso_fac_left e.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
