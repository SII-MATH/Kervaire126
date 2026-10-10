import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Data
import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Remove the sphere coefficient while retaining the actual reduced factor. -/
def sphereReducedCooperationTensorEquiv (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    reducedCooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n ≃ₗ[ZMod 2]
      LinearMap.ker (cooperationCounitF2 H R n) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  refine (directSumConcentratedEquiv
    (fun i => LinearMap.ker (cooperationCounitF2 H R i) ⊗[ZMod 2]
      mod2HomologyF2 H R (n - i) SphereSpectrum) n (fun i hi => ?_)).trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod 2) _)
        (sphereHomologyScalarEquiv H R (n - n) (sub_self n))).trans
          (TensorProduct.rid (ZMod 2) _))
  letI := H.homotopy_vanishes (n - i) (sub_ne_zero.mpr (Ne.symm hi))
  letI : Subsingleton (mod2HomologyF2 H R (n - i) SphereSpectrum) :=
    (sphereHomologyCoefficientF2Equiv H R (n - i)).injective.subsingleton
  infer_instance

variable (K : Mod2CooperationKunneth H R) [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The actual sphere boundary is an equivalence on reduced cooperations.
Neither a Milnor basis nor a differential comparison is supplied. -/
def sphereReducedBoundaryEquiv (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    LinearMap.ker (cooperationCounitF2 H R n) ≃ₗ[ZMod 2]
      mod2HomologyF2 H R (n - 1) (adamsTower H.unit SphereSpectrum 1) :=
  (sphereReducedCooperationTensorEquiv H R n).symm.trans
    (adamsNextHomologyTensorEquiv H R K SphereSpectrum n).symm

end
end KIP126.Classical.Adams
