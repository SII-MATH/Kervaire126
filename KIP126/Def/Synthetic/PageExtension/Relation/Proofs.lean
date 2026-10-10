import KIP126.Def.Synthetic.PageExtension.Relation.Data
import KIP126.Def.SpectralSequence.Crossing.Proofs

namespace KIP126.Synthetic.PageExtension
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
universe v

@[simp] theorem elementMap_zero {A : ModuleCat.{v} ℤ} :
    elementMap (0 : A) = 0 := by
  ext x
  simp [elementMap]

variable (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
  (n : ℤ) (p : ℤ × ℤ) {T : ModuleCat.{v} ℤ}
  {x : T ⟶ (E.ssData p).V} {y : T ⟶ (E.ssData (p + E.diffDeg n)).V}

theorem self_mem_targetCoset : y ∈ targetCoset E n p y := by
  simp only [targetCoset, Set.mem_setOf_eq, sub_self]
  exact Subobject.factors_zero

theorem related_target_mem_targetCoset
    (h : DifferentialRelation E n p x y)
    {z : T ⟶ (E.ssData (p + E.diffDeg n)).V}
    (hz : DifferentialRelation E n p x z) : z ∈ targetCoset E n p y :=
  DifferentialRelation.targets_sub_factors_boundary E n p h hz

/-- Essentiality tests the full ambiguity coset, not just the ordinary
classical page boundaries. -/
theorem essential_iff_zero_not_mem_targetCoset
    (h : DifferentialRelation E n p x y) :
    EssentialDifferentialRelation E n p x y ↔ 0 ∉ targetCoset E n p y := by
  simp only [EssentialDifferentialRelation, targetCoset, Set.mem_setOf_eq, sub_zero]
  exact and_iff_right h

end KIP126.Synthetic.PageExtension
