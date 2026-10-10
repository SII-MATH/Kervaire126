import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Square.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Elementary.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The double inclusion keeps the two represented cooperation factors. -/
theorem reducedCooperationSquareInclusion_lof_tmul (n k : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ (a : LinearMap.ker (cooperationCounitF2 H R k))
      (b : LinearMap.ker (cooperationCounitF2 H R (n - k))),
      reducedCooperationSquareInclusion H R n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] b)) =
        DirectSum.lof (ZMod 2) ℤ _ k (a.val ⊗ₜ[ZMod 2] b.val) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a b
  unfold reducedCooperationSquareInclusion
  erw [LinearMap.comp_apply, reducedCooperationTensorInclusion_lof_tmul]
  simp only [cooperationTensorMap, gradedTensorMapRight]
  erw [DirectSum.lmap_lof, LinearMap.lTensor_tmul]
  rfl

/-- Including both factors loses no reduced tensor. Flatness comes from
the coefficient field, not from a separate exactness assumption. -/
theorem reducedCooperationSquareInclusion_injective (n : ℤ) :
    Function.Injective (reducedCooperationSquareInclusion H R n) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  change Function.Injective
    ((cooperationTensorMap H R (fun i => LinearMap.ker (cooperationCounitF2 H R i))
      (fun i => (LinearMap.ker (cooperationCounitF2 H R i)).subtype) n) ∘
      (reducedCooperationTensorInclusion H R
        (fun i => LinearMap.ker (cooperationCounitF2 H R i)) n))
  apply Function.Injective.comp ?_
    (reducedCooperationTensorInclusion_injective H R
      (fun i => LinearMap.ker (cooperationCounitF2 H R i)) n)
  apply (DirectSum.lmap_injective _).mpr
  intro i
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (M := Mod2Cooperations H i) _ (LinearMap.ker (cooperationCounitF2 H R (n - i))).injective_subtype

end
end KIP126.StableHomotopy.Cohomology
