module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct.Binary.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Endpoint.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
open KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

/-- The actual interval boundary tensor has the cubical lifting property,
using its proved strict identification with the original binary coproduct. -/
theorem IsCubicallyCofibrant.spaceSmash_intervalBoundary {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) :
    IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint intervalBoundaryObject) X) := by
  letI (n : ℕ) := hX.level_uCompactlyGeneratedSpace n
  intro E B p hp
  exact IsCubicallyCofibrant.of_iso (isCubicallyCofibrant_binaryCoproduct hX hX)
    (spaceSmashIntervalBoundaryIso X).symm p hp

/-- The whole actual endpoint inclusion is a cubical cofibration; both
specified endpoints are retained by the original strict comparison. -/
theorem spaceSmashIntervalBoundaryMap_isCubicalCofibration {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) :
    IsCubicalCofibration (spaceSmashIntervalBoundaryMap X) := by
  letI (n : ℕ) := hX.level_uCompactlyGeneratedSpace n
  have e : spaceSmashIntervalBoundaryMap X =
      (spaceSmashIntervalBoundaryIso X).hom ≫ cylinderEndpoints X ≫
        (spaceSmashIntervalIso X).inv := by
    rw [← Category.assoc]
    change _ = (spaceSmashIntervalBoundaryComparison X ≫ cylinderEndpoints X) ≫ _
    rw [← spaceSmashIntervalBoundary_comparison_square, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [e]
  have h₁ : IsCubicalCofibration (spaceSmashIntervalBoundaryIso X).hom :=
    isCubicalCofibration_of_isIso _
  have h₂ : IsCubicalCofibration (cylinderEndpoints X) :=
    cylinderEndpoints_isCubicalCofibration hX
  have h₃ : IsCubicalCofibration (spaceSmashIntervalIso X).inv :=
    isCubicalCofibration_of_isIso _
  intro E B p hp
  exact IsCubicalCofibration.comp h₁ (IsCubicalCofibration.comp h₂ h₃) p hp

/-- The original endpoint tensor preserves stable equivalences between
cofibrant spectra, through the actual coproduct naturality square. -/
theorem spaceSmashMap_intervalBoundary_stableEquivalence {X Y : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint intervalBoundaryObject)) f) := by
  letI (n : ℕ) := hX.level_uCompactlyGeneratedSpace n
  letI (n : ℕ) := hY.level_uCompactlyGeneratedSpace n
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (coprodMap_stableEquivalence_of_isCubicallyCofibrant hX hX hY hY f f hf hf)
  haveI (Z : Prespectrum.{0}) [∀ n, UCompactlyGeneratedSpace.{0} (Z.level n)] :
      IsIso (sourceLocalization.map (spaceSmashIntervalBoundaryComparison Z)) := by
    change IsIso (sourceLocalization.map (spaceSmashIntervalBoundaryIso Z).hom)
    infer_instance
  have e := congrArg sourceLocalization.map (spaceSmashIntervalBoundaryComparison_natural f)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
