import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Normalized.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Coaction.Proofs

/-! The coaction on the next actual tower stage is determined by the existing
boundary and the coaction on the free coefficient object. This is derived
from general homology compatibility, not supplied as a tower recurrence. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The generic homology connecting map specializes to the existing Adams
boundary, with the same sign and suspension convention. -/
theorem adamsHomologyBoundary_eq_connecting (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyBoundary H X n x =
      mod2HomologyConnecting H (adamsResolutionSequence H X) n x := rfl

variable [MonoidalPreadditive C] (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) [(mod2UnitNatTrans H).CommShift ℤ]
  (hK : Mod2KunnethSuspensionCompatible H R K)

include hK in
/-- The actual next-stage boundary intertwines the actual coactions with
degree minus one, under the explicit below-page suspension compatibility. -/
theorem adamsTensorCoaction_boundary (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    mod2TensorCoaction H R K (fiber (adamsUnit H.unit X)) (n - 1)
      (adamsHomologyBoundary H X n x) =
      cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i (H.HF2 ⊗ X))
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (mod2HomologyConnectingF2 H R (adamsResolutionSequence H X)) n
        (mod2TensorCoaction H R K (H.HF2 ⊗ X) n x) :=
  mod2TensorCoaction_connecting H R K hK (adamsResolutionSequence H X) n x

include hK in
/-- A formula for the coaction on every next-stage class, using its already
constructed normalized representative. This applies in particular to every
stage `X = T_s(S⁰)`. It is not yet the polynomial Milnor coproduct formula. -/
theorem adamsTensorCoaction_next (X : C) (n : ℤ)
    (y : Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X))) :
    mod2TensorCoaction H R K (fiber (adamsUnit H.unit X)) (n - 1) y =
      cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i (H.HF2 ⊗ X))
        (fun i => mod2HomologyF2 H R i (fiber (adamsUnit H.unit X)))
        (mod2HomologyConnectingF2 H R (adamsResolutionSequence H X)) n
        (mod2TensorCoaction H R K (H.HF2 ⊗ X) n
          ((adamsHomologyKernelEquiv H R X n).symm y).val) := by
  have h := adamsTensorCoaction_boundary H R K hK X n
    ((adamsHomologyKernelEquiv H R X n).symm y).val
  rw [← adamsHomologyKernelEquiv_apply, LinearEquiv.apply_symm_apply] at h
  exact h

end

end KIP126.Classical.Adams
