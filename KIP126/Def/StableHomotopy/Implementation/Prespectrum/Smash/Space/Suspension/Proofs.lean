module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashSuspension_inv (A : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] (X : Prespectrum.{0}) :
    spaceSmashSuspension A X ≫ spaceSmashSuspensionInv A X = 𝟙 _ := by
  apply Hom.ext
  funext n
  exact congrArg BasedSpace.Hom.map (BasedSpace.smashSuspensionComparison_inverse A (X.level n))

@[simp] theorem spaceSmashSuspensionInv_hom (A : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] (X : Prespectrum.{0}) :
    spaceSmashSuspensionInv A X ≫ spaceSmashSuspension A X = 𝟙 _ := by
  apply Hom.ext
  funext n
  exact congrArg BasedSpace.Hom.map (BasedSpace.smashSuspensionInverse_comparison A (X.level n))

@[reassoc] theorem spaceSmashSuspension_natural (A : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (𝟙 A.suspension) f ≫ spaceSmashSuspension A Y =
      spaceSmashSuspension A X ≫ suspensionMap (spaceSmashMap (𝟙 A) f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  refine Quot.inductionOn a ?_
  rintro ⟨a,t⟩
  change (BasedSpace.smashSuspensionComparison A (Y.level n)).map
    ((spaceSmashMap (𝟙 A.suspension) f).level n
      (BasedSpace.smashPoint A.suspension (X.level n) (BasedSpace.suspensionProjection A (a,t)) x)) = _
  rw [spaceSmashMap_apply]
  change (BasedSpace.smashSuspensionComparison A (Y.level n)).map
    (BasedSpace.smashPoint A.suspension (Y.level n) (BasedSpace.suspensionProjection A (a,t)) (f.level n x)) = _
  rw [BasedSpace.smashSuspensionComparison_apply]
  change _ = (suspensionMap (spaceSmashMap (𝟙 A) f)).level n
    ((BasedSpace.smashSuspensionComparison A (X.level n)).map
      (BasedSpace.smashPoint A.suspension (X.level n) (BasedSpace.suspensionProjection A (a,t)) x))
  rw [BasedSpace.smashSuspensionComparison_apply]
  change _ = BasedSpace.suspensionProjection _
    ((spaceSmashMap (𝟙 A) f).level n (BasedSpace.smashPoint A (X.level n) a x),t)
  rw [spaceSmashMap_apply]
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
