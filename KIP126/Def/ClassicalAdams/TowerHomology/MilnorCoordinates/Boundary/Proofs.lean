import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Coordinates.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Elementary.Proofs

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

/-- At every tower stage the actual boundary on reduced tensors has the
derived word coordinates. No coproduct or differential comparison is input. -/
theorem sphereTowerHomologyWordEquiv_boundary_reduced (s : ℕ) (n : ℤ)
    (w : reducedCooperationTensor H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s)) (n + 1)) :
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum (s + 1)))
      (show n = (n + 1) - 1 by omega)
    sphereTowerHomologyWordEquiv H R K B (s + 1) n
      (e.symm (adamsTensorBoundary H R K (adamsTower H.unit SphereSpectrum s) (n + 1)
        (reducedCooperationTensorInclusion H R
          (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s)) (n + 1) w))) =
      reducedTensorMilnorWordEquiv H R B
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
        s (sphereTowerHomologyWordEquiv H R K B s) n w := by
  dsimp only
  rw [sphereTowerHomologyWordEquiv_succ, LinearEquiv.apply_symm_apply]
  change reducedTensorMilnorWordEquiv H R B _ s _ n
    (adamsNextHomologyTensorEquiv H R K _ _ (adamsTensorBoundary H R K _ _ _)) = _
  rw [adamsNextHomologyTensorEquiv_boundary_reduced]

/-- A reduced Milnor basis factor followed by a specified word maps under
the actual boundary to their concatenation, in every filtration and degree. -/
theorem sphereTowerHomologyWordEquiv_boundary_basis_single (s : ℕ) (n k : ℤ)
    (a : PositiveMonomial k)
    (x : mod2HomologyF2 H R (n + 1 - k) (adamsTower H.unit SphereSpectrum s))
    (d : MilnorWord s (n + (s + 1 : ℕ) - k)) (q : ZMod 2)
    (hx : (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord s t →₀ ZMod 2)
      (show n + 1 - k + s = n + (s + 1 : ℕ) - k by omega))
        (sphereTowerHomologyWordEquiv H R K B s _ x) = Finsupp.single d q) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum (s + 1)))
      (show n = (n + 1) - 1 by omega)
    sphereTowerHomologyWordEquiv H R K B (s + 1) n
      (e.symm (adamsTensorBoundary H R K (adamsTower H.unit SphereSpectrum s) (n + 1)
        (DirectSum.lof (ZMod 2) ℤ _ k ((B.basis k a).val ⊗ₜ[ZMod 2] x)))) =
      Finsupp.single (wordConsEquiv s (n + (s + 1 : ℕ)) ⟨k, a, d⟩) q := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  dsimp only
  rw [← reducedCooperationTensorInclusion_lof_tmul H R
    (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s)),
    sphereTowerHomologyWordEquiv_boundary_reduced]
  exact reducedTensorMilnorWordEquiv_basis_single H R B
    (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
    s (sphereTowerHomologyWordEquiv H R K B s) n k a x d q hx

/-- The same reduced-boundary formula on the original first quotient page,
with values in the existing normalized polynomial cochains. -/
theorem sphereFirstPageMilnorEquiv_boundary_reduced (s t : ℕ)
    (w : reducedCooperationTensor H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
      ((t : ℤ) - (s + 1 : ℕ) + 1)) :
    let n : ℤ := t - (s + 1 : ℕ)
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum (s + 1)))
      (show n = (n + 1) - 1 by omega)
    sphereFirstPageMilnorEquiv H R K B (s + 1) t
      ((adamsPageOneHomologyEquiv H.unit SphereSpectrum (s + 1 : ℕ) t).symm
        (e.symm (adamsTensorBoundary H R K (adamsTower H.unit SphereSpectrum s) (n + 1)
          (reducedCooperationTensorInclusion H R
            (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s)) (n + 1) w)))) =
      (cochainsWordEquiv (s + 1) t).symm
        ((LinearEquiv.cast (R := ZMod 2) (M := fun j => MilnorWord (s + 1) j →₀ ZMod 2)
          (show n + (s + 1 : ℕ) = t by omega))
          (reducedTensorMilnorWordEquiv H R B
            (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
            s (sphereTowerHomologyWordEquiv H R K B s) n w)) := by
  dsimp only
  change (cochainsWordEquiv (s + 1) t).symm
    ((LinearEquiv.cast (R := ZMod 2) (M := fun j => MilnorWord (s + 1) j →₀ ZMod 2)
      (show (t : ℤ) - (s + 1 : ℕ) + (s + 1 : ℕ) = t by omega))
      (sphereTowerHomologyWordEquiv H R K B (s + 1) _
        ((adamsPageOneHomologyEquiv H.unit SphereSpectrum (s + 1 : ℕ) t)
          ((adamsPageOneHomologyEquiv H.unit SphereSpectrum (s + 1 : ℕ) t).symm _)))) = _
  rw [LinearEquiv.apply_symm_apply, sphereTowerHomologyWordEquiv_boundary_reduced]

end
end KIP126.Classical.Adams
