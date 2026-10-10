import KIP126.Def.StableHomotopy.InverseSequence.Predicates

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- The projections of a Milnor triangle form a compatible cone. -/
theorem SequentialHomotopyLimit.π_step {D : InverseSequence C} {L : C}
    (H : SequentialHomotopyLimit D L) (n : ℕ) :
    H.π (n + 1) ≫ D.step n = H.π n := by
  have h := CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ _ H.distinguished
  have hn := congrArg (fun f => f ≫ Pi.π D.obj n) h
  change (H.toProduct ≫ (𝟙 _ - D.shiftMap)) ≫ Pi.π D.obj n = _ at hn
  simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
    Category.assoc, InverseSequence.shiftMap, Pi.lift_π, zero_comp] at hn
  simpa only [SequentialHomotopyLimit.π, Category.assoc] using (sub_eq_zero.mp hn).symm

/-- The explicit `1 - shift` condition means that the homotopy-limit
object vanishes; it is not a condition on an ordinary inverse limit. -/
theorem SequentialHomotopyLimit.isZero_iff {D : InverseSequence C} {L : C}
    (H : SequentialHomotopyLimit D L) : IsZero L ↔ D.IsAcyclic := by
  exact CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (CategoryTheory.Pretriangulated.Triangle.mk H.toProduct D.oneSubShift H.boundary)
    H.distinguished

end KIP126.StableHomotopy
