import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- On the first quotient page, the chosen representative of the actual
differential is a second-page boundary in the original layer group. -/
theorem adamsPageOneEquiv_d_mem_boundaries (s t : ℤ)
    (x : adamsPage unit X 1 le_rfl s t) :
    adamsPageOneEquiv unit X (s + 1) (t + 1 - 1)
      ((adamsPageD unit X 1 le_rfl (s, t) (s + 1, t + 1 - 1)).hom x) ∈
        adamsBoundaries unit X 2 (by decide) (s + 1) (t + 1 - 1) := by
  erw [adamsPageD_target]
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change adamsJ unit X (s + 1) (t + 1 - 1)
      (adamsDifferentialLift unit X 1 le_rfl s t x) ∈ _
    exact adamsDifferentialLift_boundary unit X 1 le_rfl s t x

/-- Conversely, every second-page boundary has a first-page primitive,
and its first-page representative is exactly the original layer element. -/
theorem adamsBoundary_two_exists_first_primitive (s t : ℤ)
    (z : adamsCycles unit X 2 (by decide) (s + 1) (t + 1 - 1))
    (hz : z.val ∈ adamsBoundaries unit X 2 (by decide) (s + 1) (t + 1 - 1)) :
    ∃ y : adamsPage unit X 1 le_rfl s t,
      adamsPageOneEquiv unit X (s + 1) (t + 1 - 1)
        ((adamsPageD unit X 1 le_rfl (s, t) (s + 1, t + 1 - 1)).hom y) = z.val := by
  obtain ⟨y, hy⟩ := adamsNextBoundary_is_differential unit X 1 le_rfl s t z hz
  refine ⟨y, ?_⟩
  erw [adamsPageD_target, hy]
  rfl

end
end KIP126.Classical.Adams
