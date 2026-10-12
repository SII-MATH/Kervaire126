module

public import KIP126.Def.Topology.HomotopyLifting.Cube.ClosedBall.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem cubeClosedBallHomeomorph_boundary (n : ℕ) (z : Fin n → I) :
    z ∈ _root_.Cube.boundary (Fin n) ↔ ‖(cubeClosedBallHomeomorph n z).val‖ = 1 := by
  have hn : ‖(cubeClosedBallHomeomorph n z).val‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using (cubeClosedBallHomeomorph n z).property
  constructor
  · rintro ⟨i,hi⟩
    apply le_antisymm hn
    have he : ‖(cubeClosedBallHomeomorph n z).val i‖ = 1 := by
      rcases hi with hi | hi <;> norm_num [cubeClosedBallHomeomorph,hi]
    exact he.symm.trans_le (norm_le_pi_norm _ i)
  · intro h
    by_contra hc
    have hlt : ‖(cubeClosedBallHomeomorph n z).val‖ < 1 := by
      rw [pi_norm_lt_iff zero_lt_one]
      intro i
      have hi : z i ≠ 0 ∧ z i ≠ 1 := by
        constructor
        · intro hi; exact hc ⟨i,Or.inl hi⟩
        · intro hi; exact hc ⟨i,Or.inr hi⟩
      have hlo : 0 < (z i : ℝ) := by
        have : (z i : ℝ) ≠ 0 := fun h => hi.1 (Subtype.ext h)
        exact lt_of_le_of_ne (z i).property.1 (Ne.symm this)
      have hhi : (z i : ℝ) < 1 := by
        have : (z i : ℝ) ≠ 1 := fun h => hi.2 (Subtype.ext h)
        exact lt_of_le_of_ne (z i).property.2 this
      change ‖2*(z i : ℝ)-1‖ < 1
      rw [Real.norm_eq_abs,abs_lt]
      constructor <;> linarith
    linarith


end KIP126.Topology.HomotopyLifting
