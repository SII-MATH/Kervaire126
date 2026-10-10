import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Basic.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The scalar coordinate of a degree-zero sphere coefficient, including
an explicit transport when its displayed degree is not syntactically zero. -/
def sphereHomologyScalarEquiv (n : ℤ) (hn : n = 0) :
    mod2HomologyF2 H R n SphereSpectrum ≃ₗ[ZMod 2] ZMod 2 :=
  (LinearEquiv.cast (R := ZMod 2)
    (M := fun i => mod2HomologyF2 H R i SphereSpectrum) hn).trans
      ((sphereHomologyEmptyWordEquiv H R 0).trans
        (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) emptyMilnorWord))

/-- Remove the sphere coefficient factor from the actual graded
cooperation tensor. This uses concentration in degree zero, not Künneth
or a supplied Adams-page coordinate. -/
def sphereCooperationTensorEquiv (n : ℤ) :
    letI := mod2HomologyModule H R n H.HF2
    cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n ≃ₗ[ZMod 2]
      Mod2Cooperations H n := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  refine (directSumConcentratedEquiv
    (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (n - i) SphereSpectrum)
    n (fun i hi => ?_)).trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod 2) (Mod2Cooperations H n))
        (sphereHomologyScalarEquiv H R (n - n) (sub_self n))).trans
          (TensorProduct.rid (ZMod 2) (Mod2Cooperations H n)))
  letI := H.homotopy_vanishes (n - i) (sub_ne_zero.mpr (Ne.symm hi))
  letI : Subsingleton (mod2HomologyF2 H R (n - i) SphereSpectrum) :=
    (sphereHomologyCoefficientF2Equiv H R (n - i)).injective.subsingleton
  infer_instance

end
end KIP126.Classical.Adams
