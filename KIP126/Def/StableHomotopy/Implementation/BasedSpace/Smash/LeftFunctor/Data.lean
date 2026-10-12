module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory
universe u

/-- The original quotient smash with its left factor fixed. -/
noncomputable def smashLeftFunctor (A : BasedSpace.{u}) : BasedSpace.{u} ⥤ BasedSpace.{u} where
  obj B := A.smash B
  map f := smashMap (𝟙 A) f
  map_id B := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,b⟩
    exact smashMap_apply (𝟙 A) (𝟙 B) a b
  map_comp f g := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,b⟩
    change (smashMap (𝟙 A) (f ≫ g)).map (smashPoint A _ a b) =
      (smashMap (𝟙 A) g).map ((smashMap (𝟙 A) f).map (smashPoint A _ a b))
    rw [smashMap_apply,smashMap_apply,smashMap_apply]
    rfl

/-- Exchanging the actual two quotient representatives is a strict
isomorphism, independently of their original topologies. -/
noncomputable def smashSwapIso (A B : BasedSpace.{u}) : A.smash B ≅ B.smash A where
  hom := smashSwap A B
  inv := smashSwap B A
  hom_inv_id := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,b⟩
    change (smashSwap B A).map ((smashSwap A B).map (smashPoint A B a b)) = _
    rw [smashSwap_apply,smashSwap_apply]
    rfl
  inv_hom_id := by
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨b,a⟩
    change (smashSwap A B).map ((smashSwap B A).map (smashPoint B A b a)) = _
    rw [smashSwap_apply,smashSwap_apply]
    rfl

/-- The actual exchange maps identify the two fixed-factor functors
naturally on their original continuous maps. -/
noncomputable def smashLeftRightIso (A : BasedSpace.{u}) :
    smashLeftFunctor A ≅ smashRightFunctor A :=
  NatIso.ofComponents (fun B => smashSwapIso A B) (by
    intro B C f
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨a,b⟩
    change (smashSwap A C).map ((smashMap (𝟙 A) f).map (smashPoint A B a b)) =
      (smashMap f (𝟙 A)).map ((smashSwap A B).map (smashPoint A B a b))
    rw [smashMap_apply,smashSwap_apply,smashSwap_apply,smashMap_apply])

end KIP126.StableHomotopy.Implementation.BasedSpace
