import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Elementary.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The actual boundary is inverse to the derived next-stage coordinates
on reduced tensors. No coproduct, unit, or suspension comparison is used. -/
theorem adamsNextHomologyTensorEquiv_boundary_reduced (X : C) (n : ℤ)
    (w : reducedCooperationTensor H R (fun i => mod2HomologyF2 H R i X) n) :
    adamsNextHomologyTensorEquiv H R K X n
      (adamsTensorBoundary H R K X n
        (reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n w)) = w := by
  apply reducedCooperationTensorInclusion_injective H R (fun i => mod2HomologyF2 H R i X) n
  rw [adamsTensorBoundary_normalization, cooperationTensorAugmentation_reduced_inclusion,
    map_zero, sub_zero]

/-- The reduced tensor coordinates of an elementary boundary retain its factors. -/
theorem adamsNextHomologyTensorEquiv_boundary_lof_tmul (X : C) (n k : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ (a : LinearMap.ker (cooperationCounitF2 H R k)) (x : mod2HomologyF2 H R (n - k) X),
    adamsNextHomologyTensorEquiv H R K X n
      (adamsTensorBoundary H R K X n
        (DirectSum.lof (ZMod 2) ℤ _ k (a.val ⊗ₜ[ZMod 2] x))) =
      DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a x
  rw [← reducedCooperationTensorInclusion_lof_tmul H R (fun i => mod2HomologyF2 H R i X)]
  exact adamsNextHomologyTensorEquiv_boundary_reduced H R K X n _

/-- Every next-stage homology class has an actual tensor-boundary preimage. -/
theorem adamsTensorBoundary_surjective (X : C) (n : ℤ) :
    Function.Surjective (adamsTensorBoundary H R K X n) := by
  intro y
  refine ⟨reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
    (adamsNextHomologyTensorEquiv H R K X n y), ?_⟩
  apply (adamsNextHomologyTensorEquiv H R K X n).injective
  exact adamsNextHomologyTensorEquiv_boundary_reduced H R K X n _

end
end KIP126.Classical.Adams
