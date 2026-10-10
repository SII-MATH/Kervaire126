import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Reduced.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Square.Data
import KIP126.Def.Algebra.Graded.Tensor.Lowering.Equiv.Data
import KIP126.Def.Algebra.Graded.Tensor.Associator.Data
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Lowering.Data

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

/-- Insert the normalized sphere coefficient, reassociate, and apply the actual
boundary in the right factor. This is the operation in the first-differential formula. -/
def sphereCooperationSquareBoundary (n : ℤ) :
    cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n →ₗ[ZMod 2]
      cooperationTensor H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  exact (cooperationTensorLowerMap H R
    (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
    (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    (adamsTensorBoundary H R K SphereSpectrum) n).comp
      ((gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H)
        (fun i => mod2HomologyF2 H R i SphereSpectrum) n).comp
          ((DirectSum.lof (ZMod 2) ℤ _ n).comp
            ((TensorProduct.mk (ZMod 2)
              (gradedTensor (ZMod 2) (Mod2Cooperations H) (Mod2Cooperations H) n)
              (mod2HomologyF2 H R (n - n) SphereSpectrum)).flip
              ((sphereHomologyScalarEquiv H R (n - n) (sub_self n)).symm 1))))

/-- Apply the actual sphere boundary to the second reduced factor.
This is an equivalence onto the actual next-stage reduced tensor coordinates. -/
def sphereDoubleReducedBoundaryEquiv (n : ℤ) :
    reducedCooperationSquare H R n ≃ₗ[ZMod 2]
      reducedCooperationTensor H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  exact gradedTensorLowerEquiv (R := ZMod 2)
    (V := fun i => LinearMap.ker (cooperationCounitF2 H R i))
    (W := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    (fun i => LinearMap.ker (cooperationCounitF2 H R i))
    (sphereReducedBoundaryEquiv H R K) n

/-- Two actual boundaries identify the double-reduced tensor with the
second tower stage's homology. This is derived without a Milnor basis. -/
def sphereSecondReducedBoundaryEquiv (n : ℤ) :
    reducedCooperationSquare H R n ≃ₗ[ZMod 2]
      mod2HomologyF2 H R (n - 1 - 1) (adamsTower H.unit SphereSpectrum 2) :=
  (sphereDoubleReducedBoundaryEquiv H R K n).trans
    (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) (n - 1)).symm

end
end KIP126.Classical.Adams
