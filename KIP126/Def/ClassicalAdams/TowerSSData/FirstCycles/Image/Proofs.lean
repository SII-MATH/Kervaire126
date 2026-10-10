import KIP126.Def.ClassicalAdams.TowerSSData.FirstCycles.Proofs
import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Image.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The internal E₂ class of an E₁ cycle vanishes exactly when that cycle
is an incoming d₁ boundary. No choice of Z₂ lift occurs in the criterion. -/
theorem adamsTowerE2OfFirstCycle_eq_zero_iff_is_differential (s t : ℤ)
    (z : adamsPage unit X 1 le_rfl (s + 1) t)
    (hz : adamsDifferential unit X 1 le_rfl (s + 1) t z = 0) :
    adamsTowerE2OfFirstCycle unit X (s + 1) t z hz = 0 ↔
      ∃ y : adamsPage unit X 1 le_rfl s t,
        (adamsPageD unit X 1 le_rfl (s, t) (s + 1, t)).hom y = z := by
  obtain ⟨x, hx⟩ := adamsNextCycle_exists_of_differential_eq_zero unit X
    1 le_rfl (s + 1) t z hz
  rw [adamsTowerE2OfFirstCycle_eq_zero_iff unit X (s + 1) t z hz x hx]
  have h := adamsNextBoundary_iff_is_differential unit X 1 le_rfl s t
  change ∀ x : adamsCycles unit X 2 (by omega) (s + 1) (t + 1 - 1),
    x.val ∈ adamsBoundaries unit X 2 (by omega) (s + 1) (t + 1 - 1) ↔
      ∃ y, (ModuleCat.ofHom (adamsDifferential unit X 1 le_rfl s t)).hom y =
        adamsNextCycleToPage unit X 1 le_rfl (s + 1) (t + 1 - 1) x at h
  rw [← adamsPageD_target] at h
  erw [show t + 1 - 1 = t by omega] at h
  exact (h x).trans (by rw [hx]; rfl)

end
end KIP126.Classical.Adams
