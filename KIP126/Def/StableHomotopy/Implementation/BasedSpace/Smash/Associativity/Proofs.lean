module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Associativity.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem smashMap_apply {A B C D : BasedSpace.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (a : A) (c : C) :
    (smashMap f g).map (smashPoint A C a c) = smashPoint B D (f.map a) (g.map c) :=
  (smashMap_exists f g).exists.choose_spec a c

@[simp] theorem smashSwap_apply (A B : BasedSpace.{u}) (a : A) (b : B) :
    (smashSwap A B).map (smashPoint A B a b) = smashPoint B A b a :=
  (smashCoherence_exists.2 A B).exists.choose_spec a b

@[simp] theorem smashAssoc_apply (A B C : BasedSpace.{u}) (a : A) (b : B) (c : C) :
    (smashAssoc A B C).map (smashPoint (A.smash B) C (smashPoint A B a b) c) =
      smashPoint A (B.smash C) a (smashPoint B C b c) :=
  (smashCoherence_exists.1 A B C).exists.choose_spec a b c

/-- The inverse associator has exactly the original representative
formula, with no compact-generation assumption on the input spaces. -/
@[simp] theorem smashAssocInverse_apply (A B C : BasedSpace.{u}) (a : A) (b : B) (c : C) :
    (smashAssocInverse A B C).map (smashPoint A (B.smash C) a (smashPoint B C b c)) =
      smashPoint (A.smash B) C (smashPoint A B a b) c := by
  change (smashSwap C (A.smash B)).map
    ((smashMap (𝟙 C) (smashSwap B A)).map
      ((smashAssoc C B A).map ((smashSwap A (C.smash B)).map
        ((smashMap (𝟙 A) (smashSwap B C)).map
          (smashPoint A (B.smash C) a (smashPoint B C b c)))))) = _
  simp only [smashMap_apply, smashSwap_apply, smashAssoc_apply]
  rfl

theorem smashAssoc_inverse (A B C : BasedSpace.{u}) :
    smashAssoc A B C ≫ smashAssocInverse A B C = 𝟙 _ := by
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨z, c⟩
  refine Quot.inductionOn z ?_
  rintro ⟨a, b⟩
  change (smashAssocInverse A B C).map
    ((smashAssoc A B C).map (smashPoint (A.smash B) C (smashPoint A B a b) c)) = _
  rw [smashAssoc_apply, smashAssocInverse_apply]
  rfl

theorem smashAssocInverse_assoc (A B C : BasedSpace.{u}) :
    smashAssocInverse A B C ≫ smashAssoc A B C = 𝟙 _ := by
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a, z⟩
  refine Quot.inductionOn z ?_
  rintro ⟨b, c⟩
  change (smashAssoc A B C).map
    ((smashAssocInverse A B C).map (smashPoint A (B.smash C) a (smashPoint B C b c))) = _
  rw [smashAssocInverse_apply, smashAssoc_apply]
  rfl

end KIP126.StableHomotopy.Implementation.BasedSpace
