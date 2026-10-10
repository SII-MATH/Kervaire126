import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Square.Data
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Proofs
import KIP126.Def.Algebra.Graded.Tensor.Lowering.Equiv.Proofs
import KIP126.Def.Algebra.Graded.Tensor.Associator.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Square.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

theorem sphereCooperationSquareBoundary_lof_tmul (n k : ℤ)
    (a : Mod2Cooperations H k) (b : Mod2Cooperations H (n - k)) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    sphereCooperationSquareBoundary H R K n (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] b)) =
      DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2]
        LinearEquiv.cast (R := ZMod 2)
          (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
          (show n - k - 1 = n - 1 - k by omega)
          (adamsTensorBoundary H R K SphereSpectrum (n - k)
            ((sphereCooperationTensorEquiv H R (n - k)).symm b))) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  simp only [sphereCooperationSquareBoundary, LinearMap.comp_apply]
  erw [gradedTensorAssoc_lof_tmul]
  rw [sphereHomologyScalarEquiv_cast_symm_one H R (n - n) (n - k - (n - k))
    (sub_self n) (sub_self (n - k)) (by omega)]
  change gradedTensorLowerMap (R := ZMod 2)
    (V := cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
    (W := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    (Mod2Cooperations H)
    (adamsTensorBoundary H R K SphereSpectrum) n _ = _
  erw [gradedTensorLowerMap_lof_tmul]
  rw [sphereCooperationTensorEquiv_symm_apply]
  rfl

theorem sphereDoubleReducedBoundaryEquiv_lof_tmul (n k : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ (a : LinearMap.ker (cooperationCounitF2 H R k))
      (b : LinearMap.ker (cooperationCounitF2 H R (n - k))),
    sphereDoubleReducedBoundaryEquiv H R K n (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] b)) =
      DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2]
        LinearEquiv.cast (R := ZMod 2)
          (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
          (show n - k - 1 = n - 1 - k by omega)
          (adamsTensorBoundary H R K SphereSpectrum (n - k)
            ((sphereCooperationTensorEquiv H R (n - k)).symm b.val))) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a b
  change (gradedTensorLowerEquiv (R := ZMod 2)
    (V := fun i => LinearMap.ker (cooperationCounitF2 H R i))
    (W := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    (fun i => LinearMap.ker (cooperationCounitF2 H R i))
    (sphereReducedBoundaryEquiv H R K) n).toLinearMap _ = _
  rw [gradedTensorLowerEquiv_toLinearMap, gradedTensorLowerMap_lof_tmul]
  rw [LinearEquiv.coe_coe, sphereReducedBoundaryEquiv_apply]

/-- No information is lost by taking the second reduced factor's boundary,
even when its image is regarded in the ordinary tensor coordinates. -/
theorem sphereDoubleReducedBoundary_injective (n : ℤ) :
    Function.Injective (fun w : reducedCooperationSquare H R n =>
      reducedCooperationTensorInclusion H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
        (sphereDoubleReducedBoundaryEquiv H R K n w)) :=
  (reducedCooperationTensorInclusion_injective H R _ _).comp
    (sphereDoubleReducedBoundaryEquiv H R K n).injective

/-- Reassociation followed by the actual boundary agrees with the constructed
equivalence on every double-reduced tensor, not only basis vectors. -/
theorem sphereDoubleReducedBoundaryEquiv_inclusion (n : ℤ)
    (w : reducedCooperationSquare H R n) :
    reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
      (sphereDoubleReducedBoundaryEquiv H R K n w) =
      sphereCooperationSquareBoundary H R K n (reducedCooperationSquareInclusion H R n w) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  have h : (reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)).comp
      (sphereDoubleReducedBoundaryEquiv H R K n).toLinearMap =
      (sphereCooperationSquareBoundary H R K n).comp (reducedCooperationSquareInclusion H R n) := by
    apply DirectSum.linearMap_ext
    intro k
    apply TensorProduct.ext
    ext a b : 2
    change reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
      (sphereDoubleReducedBoundaryEquiv H R K n (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] b))) =
      sphereCooperationSquareBoundary H R K n
        (reducedCooperationSquareInclusion H R n (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] b)))
    rw [sphereDoubleReducedBoundaryEquiv_lof_tmul,
      reducedCooperationTensorInclusion_lof_tmul, reducedCooperationSquareInclusion_lof_tmul]
    exact (sphereCooperationSquareBoundary_lof_tmul H R K n k a.val b.val).symm
  exact LinearMap.congr_fun h w

end
end KIP126.Classical.Adams
