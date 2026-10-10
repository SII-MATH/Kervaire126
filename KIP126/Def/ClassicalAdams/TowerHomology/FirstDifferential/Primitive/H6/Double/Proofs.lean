import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Data
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Nonvanishing.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- Both uses of the actual boundary preserve nonvanishing for this tensor. -/
theorem sphereH6DoubleTensorRepresentative_ne_zero
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) (hx : x ≠ 0) :
    sphereH6DoubleTensorRepresentative H R K a x ≠ 0 := by
  have ha' := cooperation_ne_zero_of_h6Polynomial H R B a ha
  have hy : sphereH6TensorRepresentative H R K a x ≠ 0 :=
    adamsTensorBoundary_lof_tmul_ne_zero H R K SphereSpectrum 64 64 (by decide) a ha' x hx
  exact adamsTensorBoundary_lof_tmul_ne_zero H R K (adamsTower H.unit SphereSpectrum 1)
    127 64 (by decide) a ha' (sphereH6TensorRepresentative H R K a x) hy

/-- Nonvanishing on the original first quotient page in filtration two. -/
theorem sphereAdamsPageOne_h6_double_ne_zero
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) (hx : x ≠ 0) :
    (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
      (sphereH6DoubleTensorRepresentative H R K a x) ≠ 0 := by
  intro hz
  have h := congrArg (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128) hz
  rw [LinearEquiv.apply_symm_apply, map_zero] at h
  exact sphereH6DoubleTensorRepresentative_ne_zero H R K B a ha x hx h

variable [(mod2UnitNatTrans H).CommShift ℤ]

/-- The twice-applied boundary is a genuine cycle at the second tower stage. -/
theorem sphereH6DoubleTensorRepresentative_d1_zero
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) :
    adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 2) 126
      (sphereH6DoubleTensorRepresentative H R K a x) = 0 := by
  have hp := cooperationTensorDiagonal_primitive_of_h6Polynomial H R B K hU hM a ha
  have hy : adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) 63
      (sphereH6TensorRepresentative H R K a x) = 0 :=
    sphereAdamsHomologyD1_tensorBoundary_primitive H R K hK hD hU 64 64 a hp x
  exact adamsHomologyD1_tensorBoundary_primitive H R K hK hD hU
    (adamsTower H.unit SphereSpectrum 1) 127 64 a hp
    (sphereH6TensorRepresentative H R K a x) hy

/-- The actual first-page class in bidegree (2,128) is a cycle. This does
not yet prove that its second-page class is nonzero or a specified square. -/
theorem sphereAdamsPageD_one_h6_double_zero
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) :
    (adamsPageD H.unit SphereSpectrum 1 le_rfl (2, 128) (3, 128)).hom
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H R K a x)) = 0 := by
  apply (adamsPageOneHomologyEquiv H.unit SphereSpectrum 3 128).injective
  have hd := sphereH6DoubleTensorRepresentative_d1_zero H R K B hK hD hU hM a ha x
  have h := adamsPageD_one_homologyD1 H SphereSpectrum 2 128
    ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
      (sphereH6DoubleTensorRepresentative H R K a x))
  change (adamsPageOneHomologyEquiv H.unit SphereSpectrum 3 128) _ =
    adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 2) 126
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128)
        ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
          (sphereH6DoubleTensorRepresentative H R K a x))) at h
  rw [LinearEquiv.apply_symm_apply, hd] at h
  exact h.trans (adamsPageOneHomologyEquiv H.unit SphereSpectrum 3 128).map_zero.symm

/-- The same zero-differential statement in representative-map notation. -/
theorem sphereAdamsDifferential_one_h6_double_zero
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) :
    adamsDifferential H.unit SphereSpectrum 1 le_rfl 2 128
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
        (sphereH6DoubleTensorRepresentative H R K a x)) = 0 := by
  have h := sphereAdamsPageD_one_h6_double_zero H R K B hK hD hU hM a ha x
  have ht : ((3, 128) : ℤ × ℤ) = ((2 : ℤ) + (1 : ℕ), (128 : ℤ) + (1 : ℕ) - 1) := by
    apply Prod.ext <;> omega
  rw [ht, adamsPageD_target] at h
  exact h

end
end KIP126.Classical.Adams
