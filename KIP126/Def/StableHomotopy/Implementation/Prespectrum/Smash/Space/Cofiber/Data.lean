module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cofiber.Level.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual smash of the quotient projection collapses the image
of the smashed map, giving the canonical strict comparison. -/
noncomputable def spaceSmashCofiberComparison (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    pointSetCofiber (spaceSmashMap (𝟙 A) f) ⟶ spaceSmash A (pointSetCofiber f) :=
  cofiberDesc (spaceSmashMap (𝟙 A) f) (spaceSmashMap (𝟙 A) (cofiberProjection f)) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change (spaceSmashMap (𝟙 A) (cofiberProjection f)).level n
      ((spaceSmashMap (𝟙 A) f).level n (BasedSpace.smashPoint A (X.level n) a x)) = _
    rw [spaceSmashMap_apply,spaceSmashMap_apply,cofiberProjection_image]
    exact BasedSpace.smashPoint_base_right _ _ _)

/-- The quotient interchange is a strict map in the reverse direction
when the original codomain levels are compactly generated. -/
noncomputable def spaceSmashCofiberInverse (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    spaceSmash A (pointSetCofiber f) ⟶ pointSetCofiber (spaceSmashMap (𝟙 A) f) := by
  letI := hY
  refine {
    level n := (spaceSmashCofiberInverseLevel A f n).map
    point n := (spaceSmashCofiberInverseLevel A f n).point
    bond := ?_ }
  intro n z t
  refine Quot.inductionOn z ?_
  rintro ⟨a,z⟩
  refine Quot.inductionOn z ?_
  intro y
  change (spaceSmashCofiberInverseLevel A f (n+1)).map
    ((spaceSmash A (pointSetCofiber f)).bond n
      (BasedSpace.smashPoint A ((pointSetCofiber f).level n) a (Quot.mk _ y),t)) = _
  rw [spaceSmash_bond]
  change (spaceSmashCofiberInverseLevel A f (n+1)).map
    (BasedSpace.smashPoint A (cofiberLevel f (n+1)) a (Quot.mk _ (Y.bond n (y,t)))) =
    (pointSetCofiber (spaceSmashMap (𝟙 A) f)).bond n
      ((spaceSmashCofiberInverseLevel A f n).map
        (BasedSpace.smashPoint A (cofiberLevel f n) a (Quot.mk _ y)),t)
  rw [spaceSmashCofiberInverseLevel_apply,spaceSmashCofiberInverseLevel_apply]
  change _ = Quot.mk (CofiberRelation (spaceSmashMap (𝟙 A) f) (n+1))
    ((spaceSmash A Y).bond n (BasedSpace.smashPoint A (Y.level n) a y,t))
  rw [spaceSmash_bond]
end KIP126.StableHomotopy.Implementation.Prespectrum
