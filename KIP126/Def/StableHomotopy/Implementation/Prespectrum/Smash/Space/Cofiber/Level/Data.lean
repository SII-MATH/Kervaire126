module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofiber.Level.Existence.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
noncomputable def spaceSmashCofiberInverseLevel (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (Y.level n)] :
    A.smash (cofiberLevel f n) ⟶ cofiberLevel (spaceSmashMap (𝟙 A) f) n :=
  (spaceSmashCofiberInverseLevel_exists A f n).exists.choose
end KIP126.StableHomotopy.Implementation.Prespectrum
