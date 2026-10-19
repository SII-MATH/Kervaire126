module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Family.Evaluation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Smash a fixed based space with every level of an actual prespectrum.
The retained interval is precisely the original spectrum bond interval. -/
noncomputable def spaceSmash (A : BasedSpace.{0}) (X : Prespectrum.{0}) : Prespectrum.{0} where
  level n := A.smash (X.level n)
  bond n := BasedSpace.smashFamily ContinuousMap.fst (X.bond n) (fun _ => rfl) (X.bond_point n)
  bond_point n t := BasedSpace.smashFamily_point _ _ _ _ t
  bond_zero n z := by
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    erw [BasedSpace.smashFamily_apply]
    change BasedSpace.smashPoint A (X.level (n+1)) a (X.bond n (x,0)) = _
    rw [X.bond_zero,BasedSpace.smashPoint_base_right]
  bond_one n z := by
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    erw [BasedSpace.smashFamily_apply]
    change BasedSpace.smashPoint A (X.level (n+1)) a (X.bond n (x,1)) = _
    rw [X.bond_one,BasedSpace.smashPoint_base_right]

/-- The actual pair of a based map and a strict spectrum map induces a
strict map on the fixed-space smash constructions. -/
noncomputable def spaceSmashMap {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    (a : A ⟶ B) (f : X ⟶ Y) : spaceSmash A X ⟶ spaceSmash B Y where
  level n := (BasedSpace.smashMap a ⟨f.level n,f.point n⟩).map
  point n := (BasedSpace.smashMap a ⟨f.level n,f.point n⟩).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro ⟨b,x⟩
    have hm (m : ℕ) (b : A) (x : X.level m) :
        (BasedSpace.smashMap a ⟨f.level m,f.point m⟩).map
          (BasedSpace.smashPoint A (X.level m) b x) =
          BasedSpace.smashPoint B (Y.level m) (a.map b) (f.level m x) :=
      (BasedSpace.smashMap_exists a ⟨f.level m,f.point m⟩).exists.choose_spec b x
    change (BasedSpace.smashMap a ⟨f.level (n+1),f.point (n+1)⟩).map
      (BasedSpace.smashFamily ContinuousMap.fst (X.bond n) (fun _ => rfl) (X.bond_point n)
        (BasedSpace.smashPoint A (X.level n) b x,t)) = _
    rw [BasedSpace.smashFamily_apply,hm]
    change BasedSpace.smashPoint B (Y.level (n+1)) (a.map b) (f.level (n+1) (X.bond n (x,t))) =
      BasedSpace.smashFamily ContinuousMap.fst (Y.bond n) (fun _ => rfl) (Y.bond_point n)
        ((BasedSpace.smashMap a ⟨f.level n,f.point n⟩).map (BasedSpace.smashPoint A (X.level n) b x),t)
    rw [hm,BasedSpace.smashFamily_apply,f.bond]
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
