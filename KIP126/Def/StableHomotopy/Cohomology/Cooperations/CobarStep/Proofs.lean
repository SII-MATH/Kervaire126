import KIP126.Def.StableHomotopy.Cohomology.Cooperations.CobarStep.Data
import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

theorem mod2CobarDifference_apply (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    mod2CobarDifference H R K X n x =
      K.comparison X n (mod2OuterUnitMap H X n x - mod2CoactionMap H X n x) := rfl

/-- Both unit insertions retract to the identity, so their difference lies
in the actual augmentation kernel. No shift or differential law is assumed. -/
theorem mod2CobarDifference_augmentation (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n
      (mod2CobarDifference H R K X n x) = 0 := by
  rw [mod2CobarDifference_apply, K.action_comparison, map_sub]
  change (x ≫ adamsUnit H.unit (H.HF2 ⊗ X)) ≫ mod2FreeAction H R X -
    (x ≫ mod2Coaction H X) ≫ mod2FreeAction H R X = 0
  rw [Category.assoc, Category.assoc, mod2FreeAction_outerUnit,
    mod2Coaction_counit, Category.comp_id, sub_self]

end

end KIP126.StableHomotopy.Cohomology
