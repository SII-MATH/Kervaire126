module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cone.Level.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The representative-preserving quotient comparison commutes with
the actual spectrum bonds. -/
noncomputable def spaceSmashConeComparison (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    cone (spaceSmashMap (𝟙 A) f) ⟶ spaceSmash A (cone f) where
  level n := (spaceSmashConeComparisonLevel A f n).map
  point n := (spaceSmashConeComparisonLevel A f n).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro (y | ⟨x,s⟩)
    · refine Quot.inductionOn y ?_
      rintro ⟨a,y⟩
      change (spaceSmashConeComparisonLevel A f (n+1)).map
        (Quot.mk _ (.inl ((spaceSmash A Y).bond n (BasedSpace.smashPoint A (Y.level n) a y,t)))) =
        (spaceSmash A (cone f)).bond n
          ((spaceSmashConeComparisonLevel A f n).map
            (Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y))),t)
      rw [spaceSmash_bond,spaceSmashConeComparisonLevel_inl,spaceSmashConeComparisonLevel_inl]
      change _ = (spaceSmash A (cone f)).bond n
        (BasedSpace.smashPoint A ((cone f).level n) a (Quot.mk _ (.inl y)),t)
      rw [spaceSmash_bond]
      rfl
    · refine Quot.inductionOn x ?_
      rintro ⟨a,x⟩
      change (spaceSmashConeComparisonLevel A f (n+1)).map
        (Quot.mk _ (.inr ((spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t),s))) =
        (spaceSmash A (cone f)).bond n
          ((spaceSmashConeComparisonLevel A f n).map
            (Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,s))),t)
      rw [spaceSmash_bond,spaceSmashConeComparisonLevel_inr,spaceSmashConeComparisonLevel_inr]
      change _ = (spaceSmash A (cone f)).bond n
        (BasedSpace.smashPoint A ((cone f).level n) a (Quot.mk _ (.inr (x,s))),t)
      rw [spaceSmash_bond]
      rfl

/-- Compact generation is explicitly used to reverse the ordinary
mapping-cone quotient at every level. -/
noncomputable def spaceSmashConeInverse (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hX : ∀ n, UCompactlyGeneratedSpace.{0} (X.level n))
    (hY : ∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)) :
    spaceSmash A (cone f) ⟶ cone (spaceSmashMap (𝟙 A) f) := by
  letI := hX
  letI := hY
  refine {
    level n := (spaceSmashConeInverseLevel A f n).map
    point n := (spaceSmashConeInverseLevel A f n).point
    bond := ?_ }
  intro n z t
  refine Quot.inductionOn z ?_
  rintro ⟨a,z⟩
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,s⟩)
  · change (spaceSmashConeInverseLevel A f (n+1)).map
      ((spaceSmash A (cone f)).bond n
        (BasedSpace.smashPoint A ((cone f).level n) a (Quot.mk _ (.inl y)),t)) = _
    rw [spaceSmash_bond]
    change (spaceSmashConeInverseLevel A f (n+1)).map
      (BasedSpace.smashPoint A (coneLevel f (n+1)) a (Quot.mk _ (.inl (Y.bond n (y,t))))) =
      (cone (spaceSmashMap (𝟙 A) f)).bond n
        ((spaceSmashConeInverseLevel A f n).map
          (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y))),t)
    rw [spaceSmashConeInverseLevel_inl,spaceSmashConeInverseLevel_inl]
    change _ = Quot.mk (ConeRelation (spaceSmashMap (𝟙 A) f) (n+1)) (.inl ((spaceSmash A Y).bond n (BasedSpace.smashPoint A (Y.level n) a y,t)))
    rw [spaceSmash_bond]
  · change (spaceSmashConeInverseLevel A f (n+1)).map
      ((spaceSmash A (cone f)).bond n
        (BasedSpace.smashPoint A ((cone f).level n) a (Quot.mk _ (.inr (x,s))),t)) = _
    rw [spaceSmash_bond]
    change (spaceSmashConeInverseLevel A f (n+1)).map
      (BasedSpace.smashPoint A (coneLevel f (n+1)) a (Quot.mk _ (.inr (X.bond n (x,t),s)))) =
      (cone (spaceSmashMap (𝟙 A) f)).bond n
        ((spaceSmashConeInverseLevel A f n).map
          (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,s)))),t)
    rw [spaceSmashConeInverseLevel_inr,spaceSmashConeInverseLevel_inr]
    change _ = Quot.mk (ConeRelation (spaceSmashMap (𝟙 A) f) (n+1)) (.inr ((spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t),s))
    rw [spaceSmash_bond]

end KIP126.StableHomotopy.Implementation.Prespectrum
