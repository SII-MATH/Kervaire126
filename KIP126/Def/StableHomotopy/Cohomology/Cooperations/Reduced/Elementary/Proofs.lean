import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- Inclusion of a reduced elementary tensor keeps its actual two factors. -/
theorem reducedCooperationTensorInclusion_lof_tmul (n k : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ (a : LinearMap.ker (cooperationCounitF2 H R k)) (x : V (n - k)),
    reducedCooperationTensorInclusion H R V n
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) =
        DirectSum.lof (ZMod 2) ℤ _ k (a.val ⊗ₜ[ZMod 2] x) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a x
  change (gradedTensorKernelEquiv (cooperationCounitF2 H R) V n
    (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))).val = _
  rw [gradedTensorKernelEquiv_coe, gradedTensorMap_lof_tmul]
  rfl

/-- Every included reduced tensor has augmentation zero. -/
theorem cooperationTensorAugmentation_reduced_inclusion (n : ℤ)
    (w : reducedCooperationTensor H R V n) :
    cooperationTensorAugmentation H R V n
      (reducedCooperationTensorInclusion H R V n w) = 0 :=
  (reducedCooperationAugmentationEquiv H R V n w).property

end
end KIP126.StableHomotopy.Cohomology
