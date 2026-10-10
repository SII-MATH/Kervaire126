import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Right.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Core.Algebra

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The unit-corrected actual cooperation diagonal. On reduced
cooperations this is the one-slot cobar operation, with sign kept explicit. -/
def cooperationCobarDiagonal (n : ℤ) :
    mod2HomologyF2 H R n H.HF2 →ₗ[ZMod 2]
      cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n :=
  cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n +
    cooperationTensorRightUnit H R n - cooperationTensorDiagonal H R K n

/-- Split the first cooperation factor, with both unit corrections.
This is defined on ordinary tensors; no claim of reducedness is built in. -/
def cooperationTensorCobarSplit (V : ℤ → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)] (n : ℤ) :
    cooperationTensor H R V n →ₗ[ZMod 2]
      cooperationTensor H R (cooperationTensor H R V) n :=
  cooperationTensorUnit H R (cooperationTensor H R V) n +
    cooperationTensorMap H R V (cooperationTensorUnit H R V) n -
      cooperationTensorComultiply H R K V n

end
end KIP126.StableHomotopy.Cohomology
