module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Suspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem smashSuspensionComparison_apply (A B : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] (a : A) (b : B) (t : I) :
    (smashSuspensionComparison A B).map
      (smashPoint A.suspension B (suspensionProjection A (a,t)) b) =
      suspensionProjection (A.smash B) (smashPoint A B a b,t) :=
  (smashSuspensionComparison_exists A B).exists.choose_spec a b t

@[simp] theorem smashSuspensionInverse_apply (A B : BasedSpace.{0})
    (a : A) (b : B) (t : I) :
    (smashSuspensionInverse A B).map
      (suspensionProjection (A.smash B) (smashPoint A B a b,t)) =
      smashPoint A.suspension B (suspensionProjection A (a,t)) b :=
  (smashSuspensionInverse_exists A B).exists.choose_spec a b t

@[simp] theorem smashSuspensionComparison_inverse (A B : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] :
    smashSuspensionComparison A B ≫ smashSuspensionInverse A B = 𝟙 _ := by
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,b⟩
  refine Quot.inductionOn a ?_
  rintro ⟨a,t⟩
  change (smashSuspensionInverse A B).map ((smashSuspensionComparison A B).map
    (smashPoint A.suspension B (suspensionProjection A (a,t)) b)) = _
  rw [smashSuspensionComparison_apply,smashSuspensionInverse_apply]
  rfl

@[simp] theorem smashSuspensionInverse_comparison (A B : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] :
    smashSuspensionInverse A B ≫ smashSuspensionComparison A B = 𝟙 _ := by
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨z,t⟩
  refine Quot.inductionOn z ?_
  rintro ⟨a,b⟩
  change (smashSuspensionComparison A B).map ((smashSuspensionInverse A B).map
    (suspensionProjection (A.smash B) (smashPoint A B a b,t))) = _
  rw [smashSuspensionInverse_apply,smashSuspensionComparison_apply]
  rfl

end KIP126.StableHomotopy.Implementation.BasedSpace
