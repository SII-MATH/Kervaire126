module

public import KIP126.Def.Topology.Cube.Compression.Proofs
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

namespace KIP126.Topology.Cube

open Set Metric
open scoped unitInterval

/-- Every neighborhood of an actual interior cube point contains an
open rectangular subcube whose closed coordinate intervals remain in
the original cube interior. These are the windows used by compression. -/
theorem exists_window_within {N : Type*} [Fintype N] (x : N → I)
    (hx : x ∉ _root_.Cube.boundary N) (U : Set (N → I))
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a b : N → I,
      (∀ i, 0 < a i ∧ a i < x i ∧ x i < b i ∧ b i < 1) ∧
      {t | ∀ i, a i < t i ∧ t i < b i} ⊆ U := by
  have hxi (i : N) : (0 : ℝ) < x i ∧ (x i : ℝ) < 1 := by
    constructor
    · exact lt_of_le_of_ne (x i).property.1 (fun he => hx ⟨i, Or.inl (Subtype.ext he.symm)⟩)
    · exact lt_of_le_of_ne (x i).property.2 (fun he => hx ⟨i, Or.inr (Subtype.ext he)⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  let δ (i : N) : ℝ := min (ε / 2) (min ((x i : ℝ) / 2) ((1 - (x i : ℝ)) / 2))
  have hd (i : N) : 0 < δ i := lt_min (half_pos hε)
    (lt_min (half_pos (hxi i).1) (half_pos (sub_pos.mpr (hxi i).2)))
  have hdε (i : N) : δ i ≤ ε / 2 := min_le_left _ _
  have hdx (i : N) : δ i ≤ (x i : ℝ) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hd1 (i : N) : δ i ≤ (1 - (x i : ℝ)) / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let a (i : N) : I := ⟨(x i : ℝ) - δ i, by
    constructor <;> linarith [(hxi i).1, (hxi i).2, hd i, hdx i]⟩
  let b (i : N) : I := ⟨(x i : ℝ) + δ i, by
    constructor <;> linarith [(hxi i).1, (hxi i).2, hd i, hd1 i]⟩
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    change 0 < (x i : ℝ) - δ i ∧ (x i : ℝ) - δ i < x i ∧
      (x i : ℝ) < x i + δ i ∧ (x i : ℝ) + δ i < 1
    exact ⟨by linarith [hdx i, (hxi i).1], by linarith [hd i],
      by linarith [hd i], by linarith [hd1 i, (hxi i).2]⟩
  · intro t ht
    apply hball
    apply (dist_pi_lt_iff hε).mpr
    intro i
    change |(t i : ℝ) - x i| < ε
    apply abs_lt.mpr
    have hlo : (x i : ℝ) - δ i < t i := (ht i).1
    have hhi : (t i : ℝ) < x i + δ i := (ht i).2
    constructor <;> linarith [hdε i]

end KIP126.Topology.Cube
