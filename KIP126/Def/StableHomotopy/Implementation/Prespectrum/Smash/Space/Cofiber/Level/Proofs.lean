module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofiber.Level.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
@[simp] theorem spaceSmashCofiberInverseLevel_apply (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (Y.level n)] (a : A) (y : Y.level n) :
    (spaceSmashCofiberInverseLevel A f n).map
      (BasedSpace.smashPoint A (cofiberLevel f n) a (Quot.mk _ y)) =
      Quot.mk _ (BasedSpace.smashPoint A (Y.level n) a y) :=
  (spaceSmashCofiberInverseLevel_exists A f n).exists.choose_spec a y
end KIP126.StableHomotopy.Implementation.Prespectrum
