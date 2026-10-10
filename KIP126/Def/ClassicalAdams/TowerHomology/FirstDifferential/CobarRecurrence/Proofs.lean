import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Boundary.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Sphere.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Cobar.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- A first differential after a tensor boundary splits into the
unit-corrected coproduct term and the remaining-factor differential term.
This holds for every tensor, not only primitive first factors. -/
theorem adamsHomologyD1_tensorBoundary_cobar_recurrence
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K) (X : C) (n : ℤ)
    (w : cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n) :
    reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X))) (n - 1)
      (adamsNextHomologyTensorEquiv H R K (fiber (adamsUnit H.unit X)) (n - 1)
        (adamsHomologyD1 H (fiber (adamsUnit H.unit X)) (n - 1)
          (adamsTensorBoundary H R K X n w))) =
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (adamsTensorBoundary H R K X) n
        (cooperationTensorCobarSplit H R K (fun i => mod2HomologyF2 H R i X) n w) -
      cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i X)
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (fun i => (adamsTensorBoundary H R K X i).comp
          (cooperationTensorUnit H R (fun j => mod2HomologyF2 H R j X) i)) n w := by
  rw [adamsHomologyD1_unit_sub_coaction H R K hU,
    adamsTensorCoaction_tensorBoundary H R K hK hD]
  simp only [cooperationTensorCobarSplit, LinearMap.sub_apply, LinearMap.add_apply,
    map_sub, map_add]
  rw [cooperationTensorLowerMap_unit]
  have hc := LinearMap.congr_fun (cooperationTensorLowerMap_comp H R
    (fun i => mod2HomologyF2 H R i X)
    (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
    (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
    (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X))
    (adamsTensorBoundary H R K X) n) w
  simp only [LinearMap.comp_apply] at hc
  rw [hc]
  abel

/-- For sphere coefficients the remaining-factor differential vanishes;
the first incoming tower differential is entirely the corrected coproduct term. -/
theorem sphereAdamsHomologyD1_tensorBoundary_cobar
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K) (n : ℤ)
    (w : cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum) n) :
    reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
      (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) (n - 1)
        (adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) (n - 1)
          (adamsTensorBoundary H R K SphereSpectrum n w))) =
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
        (adamsTensorBoundary H R K SphereSpectrum) n
        (cooperationTensorCobarSplit H R K (fun i => mod2HomologyF2 H R i SphereSpectrum) n w) := by
  erw [adamsHomologyD1_tensorBoundary_cobar_recurrence H R K hK hD hU SphereSpectrum n w]
  have hg : (fun i => (adamsTensorBoundary H R K SphereSpectrum i).comp
      (cooperationTensorUnit H R (fun j => mod2HomologyF2 H R j SphereSpectrum) i)) =
      (fun i => (0 : mod2HomologyF2 H R i SphereSpectrum →ₗ[ZMod 2]
        mod2HomologyF2 H R (i - 1) (adamsTower H.unit SphereSpectrum 1))) := by
    funext i
    apply LinearMap.ext
    intro x
    exact adamsTensorBoundary_unit H R K hU SphereSpectrum i x |>.trans
      (sphereAdamsHomologyD1_zero H i x)
  erw [hg]
  have hz : cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i SphereSpectrum)
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
      (fun i => (0 : mod2HomologyF2 H R i SphereSpectrum →ₗ[ZMod 2]
        mod2HomologyF2 H R (i - 1) (adamsTower H.unit SphereSpectrum 1))) n w = 0 := by
    simp only [cooperationTensorLowerMap, gradedTensorLowerMap,
      LinearMap.comp_zero, LinearMap.lTensor_zero]
    ext i
    rfl
  erw [hz, sub_zero]
  rfl

end
end KIP126.Classical.Adams
