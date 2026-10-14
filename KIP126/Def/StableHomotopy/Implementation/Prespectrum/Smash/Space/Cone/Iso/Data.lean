module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cone.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology

/-- The literal cone of a smashed map is the smash of its literal cone
when its source and target levels are compactly generated. -/
noncomputable def spaceSmashConeIso (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hX : ∀ n, UCompactlyGeneratedSpace.{0} (X.level n))
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    cone (spaceSmashMap (𝟙 A) f) ≅ spaceSmash A (cone f) where
  hom := spaceSmashConeComparison A f
  inv := spaceSmashConeInverse A f hX hY
  hom_inv_id := spaceSmashConeComparison_inverse A f hX hY
  inv_hom_id := spaceSmashConeInverse_comparison A f hX hY
end KIP126.StableHomotopy.Implementation.Prespectrum
