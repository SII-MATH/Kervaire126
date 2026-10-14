module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Associativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory
universe u

/-- The actual quotient smash, functorial in its first based-space
variable with the original second factor fixed. -/
noncomputable def smashRightFunctor (B : BasedSpace.{u}) : BasedSpace.{u} ⥤ BasedSpace.{u} where
  obj A := A.smash B
  map f := smashMap f (𝟙 B)
  map_id A := by
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
    change (smashMap (f ≫ g) (𝟙 B)).map (smashPoint _ B a b) =
      (smashMap g (𝟙 B)).map ((smashMap f (𝟙 B)).map (smashPoint _ B a b))
    rw [smashMap_apply,smashMap_apply,smashMap_apply]
    rfl

end KIP126.StableHomotopy.Implementation.BasedSpace
