module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofiber.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashCofiberComparison_apply (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ) (a : A) (y : Y.level n) :
    (spaceSmashCofiberComparison A f).level n
      (Quot.mk _ (BasedSpace.smashPoint A (Y.level n) a y)) =
      BasedSpace.smashPoint A (cofiberLevel f n) a (Quot.mk _ y) :=
  spaceSmashMap_apply (𝟙 A) (cofiberProjection f) n a y

@[simp] theorem spaceSmashCofiberComparison_inverse (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    spaceSmashCofiberComparison A f ≫ spaceSmashCofiberInverse A f hY = 𝟙 _ := by
  letI := hY
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,y⟩
  change (spaceSmashCofiberInverseLevel A f n).map
    ((spaceSmashCofiberComparison A f).level n
      (Quot.mk _ (BasedSpace.smashPoint A (Y.level n) a y))) = _
  rw [spaceSmashCofiberComparison_apply,spaceSmashCofiberInverseLevel_apply]
  rfl

@[simp] theorem spaceSmashCofiberInverse_comparison (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    spaceSmashCofiberInverse A f hY ≫ spaceSmashCofiberComparison A f = 𝟙 _ := by
  letI := hY
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,z⟩
  refine Quot.inductionOn z ?_
  intro y
  change (spaceSmashCofiberComparison A f).level n
    ((spaceSmashCofiberInverseLevel A f n).map
      (BasedSpace.smashPoint A (cofiberLevel f n) a (Quot.mk _ y))) = _
  rw [spaceSmashCofiberInverseLevel_apply,spaceSmashCofiberComparison_apply]
  rfl

@[reassoc] theorem spaceSmashCofiberComparison_projection (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    cofiberProjection (spaceSmashMap (𝟙 A) f) ≫ spaceSmashCofiberComparison A f =
      spaceSmashMap (𝟙 A) (cofiberProjection f) := rfl
end KIP126.StableHomotopy.Implementation.Prespectrum
