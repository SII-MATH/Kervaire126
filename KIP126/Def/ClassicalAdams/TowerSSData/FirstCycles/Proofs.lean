import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Data
import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Any next-cycle lift computes the same next-page class. -/
theorem adamsNextCycle_quotient_eq_of_page_eq (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (u w : adamsCycles unit X (r + 1) (by omega) s t)
    (h : adamsNextCycleToPage unit X r hr s t u =
      adamsNextCycleToPage unit X r hr s t w) :
    (adamsCycleBoundaries unit X (r + 1) (by omega) s t).mkQ u =
      (adamsCycleBoundaries unit X (r + 1) (by omega) s t).mkQ w := by
  have hb : u.val - w.val ∈ adamsBoundaries unit X r hr s t :=
    (Submodule.Quotient.eq (adamsCycleBoundaries unit X r hr s t)).mp h
  exact (Submodule.Quotient.eq (adamsCycleBoundaries unit X (r + 1) (by omega) s t)).mpr
    (adamsBoundaries_le_succ unit X r hr s t hb)

/-- The internal class agrees with every actual Z₂ representative of its E₁ cycle. -/
theorem adamsTowerE2OfFirstCycle_comparison (s t : ℤ)
    (z : adamsPage unit X 1 le_rfl s t)
    (hz : adamsDifferential unit X 1 le_rfl s t z = 0)
    (u : adamsCycles unit X 2 (by omega) s t)
    (hu : adamsNextCycleToPage unit X 1 le_rfl s t u = z) :
    (adamsTowerSSDataPageIso unit X s t 0).hom
      (adamsTowerE2OfFirstCycle unit X s t z hz) =
        (adamsCycleBoundaries unit X 2 (by omega) s t).mkQ u := by
  change (adamsTowerSSDataPageIso unit X s t 0).toLinearEquiv
    ((adamsTowerSSDataPageIso unit X s t 0).toLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply adamsNextCycle_quotient_eq_of_page_eq unit X 1 le_rfl s t
  exact (adamsNextCycle_exists_of_differential_eq_zero unit X 1 le_rfl s t z hz).choose_spec.trans hu.symm

/-- Vanishing is exactly the actual B₂ membership of any chosen lift. -/
theorem adamsTowerE2OfFirstCycle_eq_zero_iff (s t : ℤ)
    (z : adamsPage unit X 1 le_rfl s t)
    (hz : adamsDifferential unit X 1 le_rfl s t z = 0)
    (u : adamsCycles unit X 2 (by omega) s t)
    (hu : adamsNextCycleToPage unit X 1 le_rfl s t u = z) :
    adamsTowerE2OfFirstCycle unit X s t z hz = 0 ↔
      u.val ∈ adamsBoundaries unit X 2 (by omega) s t := by
  have h := (adamsTowerSSDataPageIso unit X s t 0).toLinearEquiv.map_eq_zero_iff
    (x := adamsTowerE2OfFirstCycle unit X s t z hz)
  change ((adamsTowerSSDataPageIso unit X s t 0).hom
    (adamsTowerE2OfFirstCycle unit X s t z hz) = 0 ↔
      adamsTowerE2OfFirstCycle unit X s t z hz = 0) at h
  rw [adamsTowerE2OfFirstCycle_comparison unit X s t z hz u hu] at h
  exact h.symm.trans (adamsPage_mk_eq_zero unit X 2 (by omega) s t u)

end
end KIP126.Classical.Adams
