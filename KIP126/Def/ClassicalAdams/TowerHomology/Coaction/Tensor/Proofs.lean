import KIP126.Def.ClassicalAdams.TowerHomology.Coaction.Tensor.Data

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

theorem adamsTensorBoundary_comparison (X : C) (n : ℤ)
    (z : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsTensorBoundary H R K X n (K.comparison X n z) =
      adamsHomologyBoundary H X n z := by
  change mod2HomologyConnecting H (adamsResolutionSequence H X) n
    ((K.comparison X n).symm (K.comparison X n z)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The actual normalized representative of every next-stage tensor coordinate. -/
theorem adamsNextHomologyTensorEquiv_normalized (X : C) (n : ℤ)
    (y : Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X))) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (adamsNextHomologyTensorEquiv H R K X n y) =
      K.comparison X n ((adamsHomologyKernelEquiv H R X n).symm y).val := by
  change reducedCooperationTensorInclusion H R _ n
    ((reducedCooperationAugmentationEquiv H R _ n).symm
      (adamsHomologyKunnethKernelEquiv H R K X n
        ((adamsHomologyKernelF2Equiv H R X n).symm y))) = _
  rw [reducedCooperationTensorInclusion_symm]
  rfl

/-- The tensor-coordinate boundary has the algebraic normalization formula
`inclusion(e(q(w))) = w - ρ(augmentation(w))`. This is proved from the actual
boundary; no cobar formula is assumed. -/
theorem adamsTensorBoundary_normalization (X : C) (n : ℤ)
    (w : cooperationTensor H R (fun i => mod2HomologyF2 H R i X) n) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (adamsNextHomologyTensorEquiv H R K X n (adamsTensorBoundary H R K X n w)) =
      w - mod2TensorCoaction H R K X n
        (cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n w) := by
  obtain ⟨z, rfl⟩ := (K.comparison X n).surjective w
  rw [adamsTensorBoundary_comparison, adamsNextHomologyTensorEquiv_boundary,
    map_sub, K.action_comparison]
  rfl

variable [(mod2UnitNatTrans H).CommShift ℤ]

/-- The next actual tower coaction is obtained by applying the actual
cooperation coproduct to its normalized tensor, then the actual boundary
to the remaining tensor factors. This removes the free-object coaction
from the recurrence; neither a Milnor formula nor a page comparison is input. -/
theorem adamsTensorCoaction_next_coproduct
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (X : C) (n : ℤ) (y : Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X))) :
    mod2TensorCoaction H R K (fiber (adamsUnit H.unit X)) (n - 1) y =
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (adamsTensorBoundary H R K X) n
        (cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i X) n
          (reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
            (adamsNextHomologyTensorEquiv H R K X n y))) := by
  rw [adamsNextHomologyTensorEquiv_normalized, ← hD,
    ← LinearMap.comp_apply, cooperationTensorLowerMap_comp]
  have hg : (fun i => (adamsTensorBoundary H R K X i).comp
      (K.comparison X i).toLinearMap) =
      mod2HomologyConnectingF2 H R (adamsResolutionSequence H X) := by
    funext i
    ext z
    exact adamsTensorBoundary_comparison H R K X i z
  rw [hg]
  exact adamsTensorCoaction_next H R K hK X n y

end

end KIP126.Classical.Adams
