module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofiber.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
/-- Smash preserves the actual image-collapse quotient on spectra with
compactly generated codomain levels. This is a strict point-set isomorphism. -/
noncomputable def spaceSmashCofiberIso (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    pointSetCofiber (spaceSmashMap (𝟙 A) f) ≅ spaceSmash A (pointSetCofiber f) where
  hom := spaceSmashCofiberComparison A f
  inv := spaceSmashCofiberInverse A f hY
  hom_inv_id := spaceSmashCofiberComparison_inverse A f hY
  inv_hom_id := spaceSmashCofiberInverse_comparison A f hY
end KIP126.StableHomotopy.Implementation.Prespectrum
