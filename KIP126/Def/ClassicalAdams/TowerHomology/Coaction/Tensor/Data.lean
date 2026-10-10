import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Proofs

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The actual next-stage boundary in Künneth coordinates. It is defined
from the original triangle, not from a prescribed cobar differential. -/
def adamsTensorBoundary (X : C) (n : ℤ) :
    cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n →ₗ[ZMod 2]
      mod2HomologyF2 H R (n - 1) (fiber (adamsUnit H.unit X)) :=
  (mod2HomologyConnectingF2 H R (adamsResolutionSequence H X) n).comp
    (K.comparison X n).symm.toLinearMap

end

end KIP126.Classical.Adams
