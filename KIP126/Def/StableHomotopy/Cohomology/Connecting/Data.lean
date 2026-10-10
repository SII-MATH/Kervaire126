import KIP126.Def.StableHomotopy.Context.Mapping.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The actual mod-two homology connecting map for any distinguished triangle. -/
def mod2HomologyConnecting (T : HoCofiberSequence (C := C)) (n : ℤ) :
    Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
  connectingHomomorphism (T.map (tensorLeft H.HF2)) n

/-- The same connecting map with the derived mod-two scalars. -/
def mod2HomologyConnectingF2 [MonoidalPreadditive C] (R : Mod2RingStructure H)
    (T : HoCofiberSequence (C := C)) (n : ℤ) :
    mod2HomologyF2 H R n T.Z →ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
  letI := mod2HomologyModule H R n T.Z
  letI := mod2HomologyModule H R (n - 1) T.X
  (mod2HomologyConnecting H T n).toZModLinearMap 2

end

end KIP126.StableHomotopy.Cohomology
