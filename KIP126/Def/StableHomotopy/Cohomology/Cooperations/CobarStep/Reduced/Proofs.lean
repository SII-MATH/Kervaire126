import KIP126.Def.StableHomotopy.Cohomology.Cooperations.CobarStep.Reduced.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The reduced step retains exactly the two-unit difference as representative. -/
theorem mod2CobarStep_inclusion (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (mod2CobarStep H R K X n x) =
        K.comparison X n (mod2OuterUnitMap H X n x - mod2CoactionMap H X n x) := by
  change reducedCooperationTensorInclusion H R _ n
    ((reducedCooperationAugmentationEquiv H R _ n).symm
      ⟨mod2CobarDifference H R K X n x, mod2CobarDifference_augmentation H R K X n x⟩) = _
  rw [reducedCooperationTensorInclusion_symm]
  rfl

end

end KIP126.StableHomotopy.Cohomology
