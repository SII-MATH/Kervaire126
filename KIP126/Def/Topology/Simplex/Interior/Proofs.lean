module

public import KIP126.Def.Topology.Simplex.ClosedBall.Proofs
public import KIP126.Def.Topology.Simplex.Reindex
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

@[expose] public section

namespace KIP126.Topology.Simplex

open Set Metric

/-- The actual positive-coordinate interior of the standard simplex is
Euclidean space of the expected dimension, including dimension zero. -/
theorem exists_stdSimplex_positive_homeomorph (n : ℕ) :
    Nonempty ({x : stdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < x i} ≃ₜ (Fin n → ℝ)) := by
  obtain ⟨e, he⟩ := exists_stdSimplex_closedBall_homeomorph n
  have hi (x : stdSimplex ℝ (Fin (n + 1))) :
      (∀ i, 0 < x i) ↔ ‖(e x).val‖ < 1 := by
    have hb : ‖(e x).val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (e x).property
    constructor
    · intro hx
      apply lt_of_le_of_ne hb
      intro hz
      obtain ⟨i, hi⟩ := (he x).mpr hz
      exact (ne_of_gt (hx i)) hi
    · intro hx i
      apply lt_of_le_of_ne (stdSimplex.zero_le x i)
      intro hz
      exact (ne_of_lt hx) ((he x).mp ⟨i, hz.symm⟩)
  let a : {z : Metric.closedBall (0 : Fin n → ℝ) 1 // ‖z.val‖ < 1} ≃ₜ
      Metric.ball (0 : Fin n → ℝ) 1 := {
    toFun := fun z => ⟨z.val.val, by simpa only [Metric.mem_ball, dist_zero_right] using z.property⟩
    invFun := fun z => ⟨⟨z.val, Metric.ball_subset_closedBall z.property⟩,
      by simpa only [Metric.mem_ball, dist_zero_right] using z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact ⟨(e.subtype hi).trans (a.trans Homeomorph.unitBall.symm)⟩

/-- The same actual interior description depends only on the number of
vertices, without identifying their type or their universe with `Fin`. -/
theorem exists_stdSimplex_positive_homeomorph_of_card {A : Type*} [Fintype A]
    (n : ℕ) (hA : Fintype.card A = n + 1) :
    Nonempty ({x : stdSimplex ℝ A // ∀ a, 0 < x a} ≃ₜ (Fin n → ℝ)) := by
  let e := Fintype.equivFinOfCardEq hA
  have hi (x : stdSimplex ℝ A) :
      (∀ a, 0 < x a) ↔ ∀ i, 0 < reindexHomeomorph e x i := by
    constructor
    · intro hx i
      obtain ⟨a, rfl⟩ := e.surjective i
      change 0 < stdSimplex.map e x (e a)
      rw [SimplicialRealization.simplex_map_apply_injective e e.injective]
      exact hx a
    · intro hx a
      have h := hx (e a)
      change 0 < stdSimplex.map e x (e a) at h
      rwa [SimplicialRealization.simplex_map_apply_injective e e.injective] at h
  obtain ⟨h⟩ := exists_stdSimplex_positive_homeomorph n
  exact ⟨((reindexHomeomorph e).subtype hi).trans h⟩

end KIP126.Topology.Simplex
