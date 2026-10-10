import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.CobarStep.Reduced.Proofs

/-! Derive the first differential in genuine reduced-cooperation coordinates.
The formula is not supplied by Künneth data or by MilnorCooperations. -/

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

/-- The actual first differential, in reduced tensors, is the difference
between outer-unit insertion and coaction under the homology Künneth map. -/
theorem adamsHomologyD1_tensor (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    reducedCooperationTensorInclusion H R (fun i => mod2HomologyF2 H R i X) n
      (adamsNextHomologyTensorEquiv H R K X n (adamsHomologyD1 H X n x)) =
        K.comparison X n (mod2OuterUnitMap H X n x - mod2CoactionMap H X n x) := by
  rw [adamsHomologyD1_eq_boundary_outerUnit, adamsNextHomologyTensorEquiv_boundary,
    adamsHomologyAction_outerUnit]
  rfl

/-- The reduced map was built before the tower comparison; the equality with
the actual first differential is now a theorem. -/
theorem adamsHomologyD1_eq_cobarStep (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    adamsNextHomologyTensorEquiv H R K X n (adamsHomologyD1 H X n x) =
      mod2CobarStep H R K X n x := by
  apply reducedCooperationTensorInclusion_injective H R (fun i => mod2HomologyF2 H R i X) n
  rw [adamsHomologyD1_tensor, mod2CobarStep_inclusion]

/-- The same formula for the actual quotient-page differential, including
the reindexing from Adams bidegrees to represented homology degree. -/
theorem adamsPageD_one_tensor (X : C) (s : ℕ) (t : ℤ)
    (x : adamsPage H.unit X 1 le_rfl s t) :
    let e := LinearEquiv.cast (R := ℤ)
      (M := fun n => Mod2Homology H n (adamsTower H.unit X (s + 1)))
      (show t - s - 1 = t - (s + 1 : ℕ) by omega)
    let y := adamsPageOneHomologyEquiv H.unit X s t x
    reducedCooperationTensorInclusion H R
      (fun i => mod2HomologyF2 H R i (adamsTower H.unit X s)) (t - s)
      (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit X s) (t - s)
        (e.symm (adamsPageOneHomologyEquiv H.unit X (s + 1) t
          ((adamsPageD H.unit X 1 le_rfl (s, t) ((s + 1 : ℕ), t)).hom x)))) =
        K.comparison (adamsTower H.unit X s) (t - s)
          (mod2OuterUnitMap H (adamsTower H.unit X s) (t - s) y -
            mod2CoactionMap H (adamsTower H.unit X s) (t - s) y) := by
  dsimp only
  rw [adamsPageD_one_homologyD1, LinearEquiv.symm_apply_apply]
  exact adamsHomologyD1_tensor H R K (adamsTower H.unit X s) (t - s) _

/-- The actual quotient-page differential equals the independently constructed
reduced step, after the already proved first-page and next-stage identifications. -/
theorem adamsPageD_one_cobarStep (X : C) (s : ℕ) (t : ℤ)
    (x : adamsPage H.unit X 1 le_rfl s t) :
    let e := LinearEquiv.cast (R := ℤ)
      (M := fun n => Mod2Homology H n (adamsTower H.unit X (s + 1)))
      (show t - s - 1 = t - (s + 1 : ℕ) by omega)
    adamsNextHomologyTensorEquiv H R K (adamsTower H.unit X s) (t - s)
      (e.symm (adamsPageOneHomologyEquiv H.unit X (s + 1) t
        ((adamsPageD H.unit X 1 le_rfl (s, t) ((s + 1 : ℕ), t)).hom x))) =
      mod2CobarStep H R K (adamsTower H.unit X s) (t - s)
        (adamsPageOneHomologyEquiv H.unit X s t x) := by
  dsimp only
  rw [adamsPageD_one_homologyD1, LinearEquiv.symm_apply_apply]
  exact adamsHomologyD1_eq_cobarStep H R K (adamsTower H.unit X s) (t - s) _

end

end KIP126.Classical.Adams
