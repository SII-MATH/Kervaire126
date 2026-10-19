module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Suspension.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
/-- The literal point-set smash/suspension interchange is a strict
prespectrum isomorphism, before stable localization. -/
noncomputable def spaceSmashSuspensionIso (A : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] (X : Prespectrum.{0}) :
    spaceSmash A.suspension X ≅ (spaceSmash A X).suspension where
  hom := spaceSmashSuspension A X
  inv := spaceSmashSuspensionInv A X
  hom_inv_id := spaceSmashSuspension_inv A X
  inv_hom_id := spaceSmashSuspensionInv_hom A X
end KIP126.StableHomotopy.Implementation.Prespectrum
