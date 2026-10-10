import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Coordinates.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]
  (hK : Mod2KunnethSuspensionCompatible H R K)
  (hD : Mod2KunnethDiagonalCompatible H R K)
  (hU : Mod2KunnethUnitCompatible H R K)

include hK hD hU

/-- An exact image criterion for the first differential from sphere stage
one. Every possible source is covered by actual boundary surjectivity. -/
theorem sphereAdamsHomologyD1_image_cobar_iff (n : ℤ)
    (y : Mod2Homology H (n - 1 - 1) (adamsTower H.unit SphereSpectrum 2)) :
    (∃ x : Mod2Homology H (n - 1) (adamsTower H.unit SphereSpectrum 1),
      adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) (n - 1) x = y) ↔
    ∃ w : cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n,
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
        (adamsTensorBoundary H R K SphereSpectrum) n
        (cooperationTensorCobarSplit H R K (fun i => mod2HomologyF2 H R i SphereSpectrum) n w) =
      reducedCooperationTensorInclusion H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
        (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) (n - 1) y) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨w, hw⟩ := adamsTensorBoundary_surjective H R K SphereSpectrum n x
    refine ⟨w, ?_⟩
    have h := sphereAdamsHomologyD1_tensorBoundary_cobar H R K hK hD hU n w
    rw [hw, hx] at h
    exact h.symm
  · rintro ⟨w, hw⟩
    refine ⟨adamsTensorBoundary H R K SphereSpectrum n w, ?_⟩
    apply (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) (n - 1)).injective
    apply reducedCooperationTensorInclusion_injective H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
    exact (sphereAdamsHomologyD1_tensorBoundary_cobar H R K hK hD hU n w).trans hw

/-- The exact image test on the original quotient page at the target
bidegree. It is not an assumption that the target passes the test. -/
theorem sphereAdamsPageD_one_128_image_cobar_iff
    (y : adamsPage H.unit SphereSpectrum 1 le_rfl 2 128) :
    (∃ x : adamsPage H.unit SphereSpectrum 1 le_rfl 1 128,
      (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 128) (2, 128)).hom x = y) ↔
    ∃ w : cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) 128,
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
        (adamsTensorBoundary H R K SphereSpectrum) 128
        (cooperationTensorCobarSplit H R K (fun i => mod2HomologyF2 H R i SphereSpectrum) 128 w) =
      reducedCooperationTensorInclusion H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) 127
        (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) 127
          (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128 y)) := by
  refine Iff.trans ?_ (sphereAdamsHomologyD1_image_cobar_iff H R K hK hD hU 128
    (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128 y))
  have hp (x : adamsPage H.unit SphereSpectrum 1 le_rfl 1 128) :
      adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128
        ((adamsPageD H.unit SphereSpectrum 1 le_rfl (1, 128) (2, 128)).hom x) =
      adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) 127
        (adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 128 x) :=
    adamsPageD_one_homologyD1 H SphereSpectrum 1 128 x
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 128 x,
      (hp x).symm.trans (congrArg (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128) hx)⟩
  · rintro ⟨x, hx⟩
    refine ⟨(adamsPageOneHomologyEquiv H.unit SphereSpectrum 1 128).symm x, ?_⟩
    apply (adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).injective
    rw [hp, LinearEquiv.apply_symm_apply]
    exact hx

end
end KIP126.Classical.Adams
