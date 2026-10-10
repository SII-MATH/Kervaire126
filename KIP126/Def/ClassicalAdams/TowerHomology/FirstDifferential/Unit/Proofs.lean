import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Tensor.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Proofs

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
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- Under the explicit below-page unit coherence, the actual first
differential has tensor representative `1 ⊗ x - ρ(x)`. -/
theorem adamsHomologyD1_unit_sub_coaction (hU : Mod2KunnethUnitCompatible H R K)
    (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (adamsNextHomologyTensorEquiv H R K X n (adamsHomologyD1 H X n x)) =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x -
        mod2TensorCoaction H R K X n x := by
  rw [adamsHomologyD1_eq_cobarStep]
  exact mod2CobarStep_unit_sub_coaction H R K hU X n x

/-- An actual first differential vanishes exactly when the actual
homology coaction of its source class is the elementary unit tensor.
This theorem says nothing about later differentials or permanence. -/
theorem adamsHomologyD1_eq_zero_iff (hU : Mod2KunnethUnitCompatible H R K)
    (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    adamsHomologyD1 H X n x = 0 ↔
      mod2TensorCoaction H R K X n x =
        cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x := by
  rw [← (adamsNextHomologyTensorEquiv H R K X n).map_eq_zero_iff,
    adamsHomologyD1_eq_cobarStep, mod2CobarStep_eq_zero_iff H R K hU]

/-- The same criterion for the actual quotient-page differential, with
the original first-page homology identification and degree casts. -/
theorem adamsPageD_one_eq_zero_iff (hU : Mod2KunnethUnitCompatible H R K)
    (X : C) (s : ℕ) (t : ℤ) (x : adamsPage H.unit X 1 le_rfl s t) :
    (adamsPageD H.unit X 1 le_rfl (s, t) ((s + 1 : ℕ), t)).hom x = 0 ↔
      mod2TensorCoaction H R K (adamsTower H.unit X s) (t - s)
          (adamsPageOneHomologyEquiv H.unit X s t x) =
        cooperationTensorUnit H R
          (fun i => mod2HomologyF2 H R i (adamsTower H.unit X s)) (t - s)
          (adamsPageOneHomologyEquiv H.unit X s t x) := by
  rw [← (adamsPageOneHomologyEquiv H.unit X (s + 1) t).map_eq_zero_iff,
    adamsPageD_one_homologyD1, LinearEquiv.map_eq_zero_iff]
  exact adamsHomologyD1_eq_zero_iff H R K hU (adamsTower H.unit X s) (t - s) _

end

end KIP126.Classical.Adams
