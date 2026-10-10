import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.CobarStep.Reduced.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory KIP126.Classical.Adams

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)

/-- The actual cooperation unit is group-like once the homology Künneth
comparison respects outer unit insertion. -/
theorem cooperationTensorDiagonal_unit (hU : Mod2KunnethUnitCompatible H R K) :
    cooperationTensorDiagonal H R K 0 (cooperationUnit H) =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 0
        (cooperationUnit H) := by
  rw [cooperationTensorDiagonal_apply]
  have h : cooperationDiagonalMap H 0 (cooperationUnit H) =
      mod2OuterUnitMap H H.HF2 0 (cooperationUnit H) := by
    change (H.pi0Equiv.symm 1 ≫ adamsUnit H.unit H.HF2) ≫
      H.HF2 ◁ adamsUnit H.unit H.HF2 =
      (H.pi0Equiv.symm 1 ≫ adamsUnit H.unit H.HF2) ≫ adamsUnit H.unit (H.HF2 ⊗ H.HF2)
    rw [Category.assoc, mod2AdamsUnit_naturality, Category.assoc]
  rw [h, hU]

/-- The independently defined reduced step has the ordinary unit-minus-
coaction representative. No tower differential appears in this theorem. -/
theorem mod2CobarStep_unit_sub_coaction (hU : Mod2KunnethUnitCompatible H R K)
    (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (mod2CobarStep H R K X n x) =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x -
        mod2TensorCoaction H R K X n x := by
  rw [mod2CobarStep_inclusion, map_sub, hU]
  rfl

/-- Vanishing of the reduced step means precisely that the class has
trivial coaction. This is only a first-step condition, not permanence. -/
theorem mod2CobarStep_eq_zero_iff (hU : Mod2KunnethUnitCompatible H R K)
    (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    mod2CobarStep H R K X n x = 0 ↔
      mod2TensorCoaction H R K X n x =
        cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x := by
  constructor
  · intro hx
    have h := mod2CobarStep_unit_sub_coaction H R K hU X n x
    rw [hx, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm
  · intro hx
    apply reducedCooperationTensorInclusion_injective H R
      (fun i => mod2HomologyF2 H R i X) n
    rw [map_zero, mod2CobarStep_unit_sub_coaction H R K hU, hx, sub_self]

end KIP126.StableHomotopy.Cohomology
