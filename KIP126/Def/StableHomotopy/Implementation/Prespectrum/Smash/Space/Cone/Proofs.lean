module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cone.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashConeComparison_inverse (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hX : ∀ n, UCompactlyGeneratedSpace.{0} (X.level n))
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    spaceSmashConeComparison A f ≫ spaceSmashConeInverse A f hX hY = 𝟙 _ := by
  letI := hX
  letI := hY
  apply Hom.ext
  funext n
  exact congrArg BasedSpace.Hom.map (spaceSmashConeComparisonLevel_inverse A f n)

@[simp] theorem spaceSmashConeInverse_comparison (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hX : ∀ n, UCompactlyGeneratedSpace.{0} (X.level n))
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    spaceSmashConeInverse A f hX hY ≫ spaceSmashConeComparison A f = 𝟙 _ := by
  letI := hX
  letI := hY
  apply Hom.ext
  funext n
  exact congrArg BasedSpace.Hom.map (spaceSmashConeInverseLevel_comparison A f n)

/-- The actual comparison preserves the specified inclusion of the
codomain into the literal mapping cone. -/
@[reassoc] theorem spaceSmashConeComparison_inclusion (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    coneInclusion (spaceSmashMap (𝟙 A) f) ≫ spaceSmashConeComparison A f =
      spaceSmashMap (𝟙 A) (coneInclusion f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,y⟩
  change (spaceSmashConeComparisonLevel A f n).map
    (Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y))) =
    (spaceSmashMap (𝟙 A) (coneInclusion f)).level n (BasedSpace.smashPoint A (Y.level n) a y)
  rw [spaceSmashConeComparisonLevel_inl,spaceSmashMap_apply]
  rfl
end KIP126.StableHomotopy.Implementation.Prespectrum
