module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofiber.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cone.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- The cone and quotient smash comparisons respect the actual collapse
map. No stable-excision identification is used in this strict square. -/
@[reassoc] theorem spaceSmashConeComparison_toCofiber (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    coneToCofiber (spaceSmashMap (𝟙 A) f) ≫ spaceSmashCofiberComparison A f =
      spaceSmashConeComparison A f ≫ spaceSmashMap (𝟙 A) (coneToCofiber f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · refine Quot.inductionOn y ?_
    rintro ⟨a,y⟩
    change (spaceSmashCofiberComparison A f).level n
      (Quot.mk _ (BasedSpace.smashPoint A (Y.level n) a y)) =
      (spaceSmashMap (𝟙 A) (coneToCofiber f)).level n
        ((spaceSmashConeComparisonLevel A f n).map
          (Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y))))
    rw [spaceSmashCofiberComparison_apply,spaceSmashConeComparisonLevel_inl]
    change _ = (spaceSmashMap (𝟙 A) (coneToCofiber f)).level n
      (BasedSpace.smashPoint A ((cone f).level n) a (Quot.mk _ (.inl y)))
    rw [spaceSmashMap_apply]
    rfl
  · refine Quot.inductionOn x ?_
    rintro ⟨a,x⟩
    change (spaceSmashCofiberComparison A f).level n
      ((pointSetCofiber (spaceSmashMap (𝟙 A) f)).level n).point =
      (spaceSmashMap (𝟙 A) (coneToCofiber f)).level n
        ((spaceSmashConeComparisonLevel A f n).map
          (Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,t))))
    rw [(spaceSmashCofiberComparison A f).point,spaceSmashConeComparisonLevel_inr]
    change _ = (spaceSmashMap (𝟙 A) (coneToCofiber f)).level n
      (BasedSpace.smashPoint A ((cone f).level n) a (Quot.mk _ (.inr (x,t))))
    rw [spaceSmashMap_apply]
    exact (BasedSpace.smashPoint_base_right A (cofiberLevel f n) a).symm
end KIP126.StableHomotopy.Implementation.Prespectrum
