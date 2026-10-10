import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- A next-page cycle is a next-page boundary exactly when its current-page
class is hit by the incoming differential. -/
theorem adamsNextBoundary_iff_is_differential (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsCycles unit X (r + 1) (Nat.succ_pos r) (s + r) (t + r - 1)) :
    x.val ∈ adamsBoundaries unit X (r + 1) (Nat.succ_pos r) (s + r) (t + r - 1) ↔
      ∃ y : adamsPage unit X r hr s t,
        adamsDifferential unit X r hr s t y =
          adamsNextCycleToPage unit X r hr (s + r) (t + r - 1) x := by
  constructor
  · exact adamsNextBoundary_is_differential unit X r hr s t x
  · intro h
    apply (adamsNextCycleToHomology_eq_zero_iff unit X r hr (s + r, t + r - 1) x).mp
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (adamsModuleCatBoundary_iff unit X r hr s t _).mpr h

end
end KIP126.Classical.Adams
