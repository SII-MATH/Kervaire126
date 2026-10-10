import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Suspension.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Lowering.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Connecting.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) [(tensorLeft H.HF2).CommShift ℤ]
  (hK : Mod2KunnethSuspensionCompatible H R K)
  [(tensorLeft H.HF2).IsTriangulated]

include hK in
/-- Boundary compatibility follows from Künneth naturality and suspension
compatibility, for every distinguished triangle. It is not an Adams input. -/
theorem mod2Kunneth_connecting (T : HoCofiberSequence (C := C)) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ T.Z)) :
    K.comparison T.X (n - 1)
      (mod2HomologyConnecting H (T.map (tensorLeft H.HF2)) n x) =
      cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i T.Z)
        (fun i => mod2HomologyF2 H R i T.X) (mod2HomologyConnectingF2 H R T) n
        (K.comparison T.Z n x) := by
  rw [mod2HomologyConnecting_map_factor, hK, K.naturality]
  have hg : (fun i => (mod2HomologyDesuspendF2 H R T.X i).comp
      ((mod2HomologyF2Map H R T.h i).hom)) = mod2HomologyConnectingF2 H R T := by
    funext i
    ext z
    exact (mod2HomologyConnecting_factor H T i z).symm
  rw [← LinearMap.comp_apply, cooperationTensorLowerMap_comp, hg]

end KIP126.StableHomotopy.Cohomology
