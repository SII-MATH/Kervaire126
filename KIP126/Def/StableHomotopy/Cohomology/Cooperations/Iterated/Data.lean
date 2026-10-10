import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Iterate the shifted reduced-cooperation tensor operation. This is an
algebraic graded module, not an assumed page of an Adams spectral sequence. -/
def iteratedReducedCooperations (V : ℤ → ModuleCat.{v} (ZMod 2)) :
    ℕ → ℤ → ModuleCat.{v} (ZMod 2)
  | 0, n => V n
  | s + 1, n => ModuleCat.of (ZMod 2)
      (reducedCooperationTensor H R (fun i => iteratedReducedCooperations V s i) (n + 1))

end

end KIP126.StableHomotopy.Cohomology
