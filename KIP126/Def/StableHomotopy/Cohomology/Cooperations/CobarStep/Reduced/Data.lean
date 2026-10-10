import KIP126.Def.StableHomotopy.Cohomology.Cooperations.CobarStep.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- A reduced cobar step built from the coefficient unit and Künneth, before
comparison with the Adams tower's first differential. -/
def mod2CobarStep (X : C) (n : ℤ) :
    mod2HomologyF2 H R n X →ₗ[ZMod 2]
      reducedCooperationTensor H R (fun i => mod2HomologyF2 H R i X) n :=
  (reducedCooperationAugmentationEquiv H R (fun i => mod2HomologyF2 H R i X) n).symm.toLinearMap.comp
    ((mod2CobarDifference H R K X n).codRestrict _ (mod2CobarDifference_augmentation H R K X n))

end

end KIP126.StableHomotopy.Cohomology
