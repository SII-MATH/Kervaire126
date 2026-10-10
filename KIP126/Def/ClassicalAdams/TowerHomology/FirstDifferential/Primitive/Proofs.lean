import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Boundary.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Sphere.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Primitive.Proofs

/-! A primitive cooperation carries an actual first-cycle coefficient to
an actual first cycle in the next tower stage. No Milnor or Lin input is
used in this general theorem. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- Applying the genuine boundary to a primitive tensor over a first cycle
produces a first cycle at the next actual tower stage. -/
theorem adamsHomologyD1_tensorBoundary_primitive
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K) (X : C) (n k : ℤ)
    (a : Mod2Cooperations H k)
    (ha : cooperationTensorDiagonal H R K k a =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) k a +
        cooperationTensorRightUnit H R k a)
    (x : Mod2Homology H (n - k) X) (hx : adamsHomologyD1 H X (n - k) x = 0) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    adamsHomologyD1 H (fiber (adamsUnit H.unit X)) (n - 1)
      (adamsTensorBoundary H R K X n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))) = 0 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  apply (adamsHomologyD1_eq_zero_iff H R K hU _ _ _).mpr
  rw [adamsTensorCoaction_tensorBoundary H R K hK hD,
    cooperationTensorComultiply_primitive H R K _ n k a ha, map_add,
    cooperationTensorLowerMap_unit]
  have hz :
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (adamsTensorBoundary H R K X) n
        (cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X)) n
          (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))) = 0 := by
    rw [← LinearMap.comp_apply, cooperationTensorLowerMap_comp]
    simp only [cooperationTensorLowerMap, gradedTensorLowerMap_lof_tmul,
      LinearMap.comp_apply]
    rw [adamsTensorBoundary_unit H R K hU, hx]
    erw [map_zero, TensorProduct.tmul_zero, map_zero]
  rw [hz, add_zero]

/-- Sphere coefficients are already first cycles, so no coefficient-cycle
hypothesis remains for the first nontrivial sphere tower stage. -/
theorem sphereAdamsHomologyD1_tensorBoundary_primitive
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K) (n k : ℤ)
    (a : Mod2Cooperations H k)
    (ha : cooperationTensorDiagonal H R K k a =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) k a +
        cooperationTensorRightUnit H R k a)
    (x : Mod2Homology H (n - k) SphereSpectrum) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    adamsHomologyD1 H (fiber (adamsUnit H.unit SphereSpectrum)) (n - 1)
      (adamsTensorBoundary H R K SphereSpectrum n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))) = 0 :=
  adamsHomologyD1_tensorBoundary_primitive H R K hK hD hU SphereSpectrum n k a ha x
    (sphereAdamsHomologyD1_zero H (n - k) x)

/-- The cycle statement on the actual first quotient page in filtration one,
using the existing homology/page isomorphism rather than a new page model. -/
theorem sphereAdamsPageD_one_tensorBoundary_primitive
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K) (n k : ℤ)
    (a : Mod2Cooperations H k)
    (ha : cooperationTensorDiagonal H R K k a =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) k a +
        cooperationTensorRightUnit H R k a)
    (x : Mod2Homology H (n - k) SphereSpectrum) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    let y := adamsTensorBoundary H R K SphereSpectrum n
      (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))
    (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, n) (2, n)).hom
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 n).symm y) = 0 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  dsimp only
  apply (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 n).injective
  have hd := sphereAdamsHomologyD1_tensorBoundary_primitive H R K hK hD hU n k a ha x
  have h := adamsPageD_one_homologyD1 H SphereSpectrum 1 n
    ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 n).symm
      (adamsTensorBoundary H R K SphereSpectrum n
        (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x))))
  erw [LinearEquiv.apply_symm_apply, hd, map_zero] at h
  exact h.trans (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 n).map_zero.symm

end

end KIP126.Classical.Adams
