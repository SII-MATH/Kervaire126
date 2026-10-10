import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Representatives of the same quotient class have exactly the same
liftability at every tower stage, not merely at the next page. -/
theorem adamsCycles_mem_iff_of_page_eq (r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (s t : ℤ) (z w : adamsCycles unit X r hr s t)
    (h : (adamsCycleBoundaries unit X r hr s t).mkQ z =
      (adamsCycleBoundaries unit X r hr s t).mkQ w) :
    z.val ∈ adamsCycles unit X q hq s t ↔ w.val ∈ adamsCycles unit X q hq s t := by
  have hd : z.val - w.val ∈ adamsBoundaries unit X r hr s t :=
    (Submodule.Quotient.eq (adamsCycleBoundaries unit X r hr s t)).mp h
  have hdZ : z.val - w.val ∈ adamsCycles unit X q hq s t := by
    obtain ⟨a, _, ha⟩ := hd
    rw [← ha]
    exact adamsJ_mem_cycles unit X q hq s t a
  constructor
  · intro hz
    exact (adamsCycles unit X q hq s t).sub_mem_iff_right hz |>.mp hdZ
  · intro hw
    exact (adamsCycles unit X q hq s t).sub_mem_iff_left hw |>.mp hdZ

end
end KIP126.Classical.Adams
