import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Unit.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Lowering.Proofs

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

/-- The actual tensor-coordinate boundary is a comodule map of degree
minus one. This formula holds for arbitrary tensors, not just normalized
ones. It is derived from the actual connecting map and Künneth coherence. -/
theorem adamsTensorCoaction_tensorBoundary
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K) (X : C) (n : ℤ)
    (w : cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n) :
    mod2TensorCoaction H R K (fiber (adamsUnit H.unit X)) (n - 1)
        (adamsTensorBoundary H R K X n w) =
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (adamsTensorBoundary H R K X) n
        (cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i X) n w) := by
  obtain ⟨z, rfl⟩ := (K.comparison X n).surjective w
  rw [adamsTensorBoundary_comparison, adamsTensorCoaction_boundary H R K hK,
    ← hD]
  have hg : (fun i => (adamsTensorBoundary H R K X i).comp
      (K.comparison X i).toLinearMap) =
      mod2HomologyConnectingF2 H R (adamsResolutionSequence H X) := by
    funext i
    ext z
    exact adamsTensorBoundary_comparison H R K X i z
  have hc := cooperationTensorLowerMap_comp H R
    (fun i => mod2HomologyF2 H R i (H.HF2 ⊗ X))
    (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
    (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
    (fun i => (K.comparison X i).toLinearMap) (adamsTensorBoundary H R K X) n
  rw [hg] at hc
  exact (LinearMap.congr_fun hc (mod2TensorCoaction H R K (H.HF2 ⊗ X) n z)).symm

/-- The unit tensor is sent to the actual first differential, not to a
prescribed algebraic differential. -/
theorem adamsTensorBoundary_unit (hU : Mod2KunnethUnitCompatible H R K)
    (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    adamsTensorBoundary H R K X n
      (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x) =
      adamsHomologyD1 H X n x := by
  rw [← hU, adamsTensorBoundary_comparison, adamsHomologyD1_eq_boundary_outerUnit]

end

end KIP126.Classical.Adams
