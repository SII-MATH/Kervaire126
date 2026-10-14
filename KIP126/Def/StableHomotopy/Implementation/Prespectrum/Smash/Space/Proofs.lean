module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmash_bond (A : BasedSpace.{0}) (X : Prespectrum.{0})
    (n : ℕ) (a : A) (x : X.level n) (t : I) :
    (spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t) =
      BasedSpace.smashPoint A (X.level (n+1)) a (X.bond n (x,t)) :=
  BasedSpace.smashFamily_apply ContinuousMap.fst (X.bond n) (fun _ => rfl) (X.bond_point n) a x t

@[simp] theorem spaceSmashMap_apply {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    (a : A ⟶ B) (f : X ⟶ Y) (n : ℕ) (b : A) (x : X.level n) :
    (spaceSmashMap a f).level n (BasedSpace.smashPoint A (X.level n) b x) =
      BasedSpace.smashPoint B (Y.level n) (a.map b) (f.level n x) :=
  (BasedSpace.smashMap_exists a ⟨f.level n,f.point n⟩).exists.choose_spec b x

@[simp] theorem spaceSmashMap_id (A : BasedSpace.{0}) (X : Prespectrum.{0}) :
    spaceSmashMap (𝟙 A) (𝟙 X) = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  exact spaceSmashMap_apply (𝟙 A) (𝟙 X) n a x

@[simp] theorem spaceSmashMap_comp {A B C : BasedSpace.{0}} {X Y Z : Prespectrum.{0}}
    (a : A ⟶ B) (b : B ⟶ C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    spaceSmashMap (a ≫ b) (f ≫ g) = spaceSmashMap a f ≫ spaceSmashMap b g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨c,x⟩
  change (spaceSmashMap (a ≫ b) (f ≫ g)).level n (BasedSpace.smashPoint A (X.level n) c x) =
    (spaceSmashMap b g).level n ((spaceSmashMap a f).level n (BasedSpace.smashPoint A (X.level n) c x))
  rw [spaceSmashMap_apply,spaceSmashMap_apply,spaceSmashMap_apply]
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
