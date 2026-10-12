module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Suspension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Strict comparison carrying the sphere-factor suspension coordinate
unchanged past the spectrum structure coordinate. -/
noncomputable def spaceSmashSuspension (A : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] (X : Prespectrum.{0}) :
    spaceSmash A.suspension X ⟶ (spaceSmash A X).suspension where
  level n := (BasedSpace.smashSuspensionComparison A (X.level n)).map
  point n := (BasedSpace.smashSuspensionComparison A (X.level n)).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    change (BasedSpace.smashSuspensionComparison A (X.level (n+1))).map
      ((spaceSmash A.suspension X).bond n
        (BasedSpace.smashPoint A.suspension (X.level n) (BasedSpace.suspensionProjection A (a,s)) x,t)) = _
    rw [spaceSmash_bond,BasedSpace.smashSuspensionComparison_apply]
    change _ = (suspension (spaceSmash A X)).bond n
      ((BasedSpace.smashSuspensionComparison A (X.level n)).map
        (BasedSpace.smashPoint A.suspension (X.level n) (BasedSpace.suspensionProjection A (a,s)) x),t)
    rw [BasedSpace.smashSuspensionComparison_apply]
    change _ = BasedSpace.suspensionProjection _
      ((spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t),s)
    rw [spaceSmash_bond]
    rfl

/-- The reverse interchange is itself a strict prespectrum map. -/
noncomputable def spaceSmashSuspensionInv (A : BasedSpace.{0}) (X : Prespectrum.{0}) :
    (spaceSmash A X).suspension ⟶ spaceSmash A.suspension X where
  level n := (BasedSpace.smashSuspensionInverse A (X.level n)).map
  point n := (BasedSpace.smashSuspensionInverse A (X.level n)).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro ⟨z,s⟩
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change (BasedSpace.smashSuspensionInverse A (X.level (n+1))).map
      (BasedSpace.suspensionProjection _
        ((spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t),s)) = _
    rw [spaceSmash_bond,BasedSpace.smashSuspensionInverse_apply]
    change _ = (spaceSmash A.suspension X).bond n
      ((BasedSpace.smashSuspensionInverse A (X.level n)).map
        (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint A (X.level n) a x,s)),t)
    rw [BasedSpace.smashSuspensionInverse_apply,spaceSmash_bond]

end KIP126.StableHomotopy.Implementation.Prespectrum
