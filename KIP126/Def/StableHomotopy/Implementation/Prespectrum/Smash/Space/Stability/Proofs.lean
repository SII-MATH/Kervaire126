module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Suspension.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal zero-sphere factor preserves actual stable equivalences,
including for spectra whose levels are not assumed compactly generated. -/
theorem spaceSmashMap_zeroSphere_stableEquivalence {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 BasedSpace.zeroSphere) f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ hf
  letI := stableEquivalences.Q_inverts _ (spaceSmashUnit_stableEquivalence X)
  letI := stableEquivalences.Q_inverts _ (spaceSmashUnit_stableEquivalence Y)
  have h := congrArg sourceLocalization.map (spaceSmashUnit_natural f)
  simp only [Functor.map_comp] at h
  exact IsIso.of_isIso_fac_right h

/-- Once smash with a space preserves the particular equivalence, its
actual suspension does so too, by the strict interchange isomorphism. -/
theorem spaceSmashMap_suspension_stableEquivalence (A : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hf : stableEquivalences (spaceSmashMap (𝟙 A) f)) :
    stableEquivalences (spaceSmashMap (𝟙 A.suspension) f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (suspensionMap_stableEquivalence _ hf)
  haveI (Z : Prespectrum.{0}) : IsIso (sourceLocalization.map (spaceSmashSuspension A Z)) := by
    change IsIso (sourceLocalization.map (spaceSmashSuspensionIso A Z).hom)
    infer_instance
  have h := congrArg sourceLocalization.map (spaceSmashSuspension_natural A f)
  simp only [Functor.map_comp] at h
  exact IsIso.of_isIso_fac_right h

/-- Each fixed point-set sphere has the actual good-space properties. -/
theorem sphereLevel_good (n : ℕ) : (sphereLevel n).IsGood := by
  induction n with
  | zero => exact BasedSpace.good_zeroSphere
  | succ n ih => exact BasedSpace.good_suspension ih

/-- Every actual sphere factor preserves stable equivalences. This is the
sphere step of fixed-CW smash invariance, proved from the explicit models. -/
theorem spaceSmashMap_sphere_stableEquivalence (n : ℕ) {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (sphereLevel n)) f) := by
  induction n with
  | zero => exact spaceSmashMap_zeroSphere_stableEquivalence f hf
  | succ n ih =>
    letI := (sphereLevel_good n).1
    exact spaceSmashMap_suspension_stableEquivalence (sphereLevel n) f ih

end KIP126.StableHomotopy.Implementation.Prespectrum
