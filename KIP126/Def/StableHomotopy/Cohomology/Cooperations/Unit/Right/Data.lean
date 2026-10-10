import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The elementary tensor `a ⊗ 1`, in its actual degree-`n` summand. -/
def cooperationTensorRightUnit (n : ℤ) :
    mod2HomologyF2 H R n H.HF2 →ₗ[ZMod 2]
      cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  (DirectSum.lof (ZMod 2) ℤ _ n).comp
    ((TensorProduct.mk (ZMod 2) (Mod2Cooperations H n)
      (mod2HomologyF2 H R (n - n) H.HF2)).flip
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
          (sub_self n).symm) (cooperationUnit H)))

end

end KIP126.StableHomotopy.Cohomology
