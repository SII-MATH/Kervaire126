import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Data
import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The two actual unit insertions, subtracted and expressed by Künneth.
This definition does not use any tower page or differential. -/
def mod2CobarDifference (X : C) (n : ℤ) :
    mod2HomologyF2 H R n X →ₗ[ZMod 2]
      cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n :=
  letI := mod2HomologyModule H R n X
  letI := mod2HomologyModule H R n (H.HF2 ⊗ X)
  (K.comparison X n).toLinearMap.comp
    ((mod2OuterUnitMap H X n - mod2CoactionMap H X n).toZModLinearMap 2)

end

end KIP126.StableHomotopy.Cohomology
