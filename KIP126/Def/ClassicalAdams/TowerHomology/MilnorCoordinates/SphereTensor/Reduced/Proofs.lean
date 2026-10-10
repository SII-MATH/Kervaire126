import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Data
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Coordinates.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

theorem sphereReducedCooperationTensorEquiv_symm_apply (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
    (sphereReducedCooperationTensorEquiv H R n).symm a =
      DirectSum.lof (ZMod 2) ℤ _ n
        (a ⊗ₜ[ZMod 2] (sphereHomologyScalarEquiv H R (n - n) (sub_self n)).symm 1) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  simp [sphereReducedCooperationTensorEquiv, directSumConcentratedEquiv,
    TensorProduct.congr_symm, TensorProduct.rid_symm_apply, TensorProduct.congr_tmul]
  rfl

theorem sphereReducedCooperationTensorEquiv_inclusion (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n
      ((sphereReducedCooperationTensorEquiv H R n).symm a) =
      (sphereCooperationTensorEquiv H R n).symm a.val := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  rw [sphereReducedCooperationTensorEquiv_symm_apply,
    reducedCooperationTensorInclusion_lof_tmul, sphereCooperationTensorEquiv_symm_apply]

variable (K : Mod2CooperationKunneth H R) [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The constructed equivalence really is the existing tower boundary. -/
theorem sphereReducedBoundaryEquiv_apply (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
    sphereReducedBoundaryEquiv H R K n a =
      adamsTensorBoundary H R K SphereSpectrum n
        ((sphereCooperationTensorEquiv H R n).symm a.val) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  apply (adamsNextHomologyTensorEquiv H R K SphereSpectrum n).injective
  change adamsNextHomologyTensorEquiv H R K SphereSpectrum n
    ((adamsNextHomologyTensorEquiv H R K SphereSpectrum n).symm
      ((sphereReducedCooperationTensorEquiv H R n).symm a)) = _
  rw [LinearEquiv.apply_symm_apply, ← sphereReducedCooperationTensorEquiv_inclusion,
    adamsNextHomologyTensorEquiv_boundary_reduced]

end
end KIP126.Classical.Adams
