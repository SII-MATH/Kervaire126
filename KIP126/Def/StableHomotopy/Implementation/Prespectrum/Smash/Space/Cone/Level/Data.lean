module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cone.Level.Existence.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
noncomputable def spaceSmashConeComparisonLevel (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ) :
    coneLevel (spaceSmashMap (𝟙 A) f) n ⟶ A.smash (coneLevel f n) :=
  (spaceSmashConeComparison_exists A f n).exists.choose

noncomputable def spaceSmashConeInverseLevel (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (X.level n)] [UCompactlyGeneratedSpace.{0} (Y.level n)] :
    A.smash (coneLevel f n) ⟶ coneLevel (spaceSmashMap (𝟙 A) f) n :=
  (spaceSmashConeInverse_exists A f n).exists.choose
end KIP126.StableHomotopy.Implementation.Prespectrum
