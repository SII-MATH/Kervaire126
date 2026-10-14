module

public import KIP126.Def.Topology.Cube.Compression.Data
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

variable {N : Type*} (a b : N → I) (hab : ∀ i, a i < b i)
include hab

/-- Points below the chosen interval map to its original zero endpoint. -/
theorem windowCompression_apply_of_le (x : N → I) (i : N) (hx : x i ≤ a i) :
    windowCompression a b x i = 0 := by
  apply projIcc_eq_zero.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (show (x i : ℝ) ≤ a i from hx))
    (sub_nonneg.mpr (show (a i : ℝ) ≤ b i from (hab i).le))

/-- Points above the chosen interval map to its original one endpoint. -/
theorem windowCompression_apply_of_ge (x : N → I) (i : N) (hx : b i ≤ x i) :
    windowCompression a b x i = 1 := by
  apply projIcc_eq_one.mpr
  apply (le_div_iff₀ (sub_pos.mpr (show (a i : ℝ) < b i from hab i))).mpr
  simpa only [one_mul] using sub_le_sub_right
    (show (b i : ℝ) ≤ x i from hx) (a i : ℝ)

/-- Every boundary point still lies on an original boundary face. -/
theorem windowCompression_preserves_boundary (x : N → I)
    (hx : x ∈ _root_.Cube.boundary N) :
    windowCompression a b x ∈ _root_.Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := hx
  · exact ⟨i, Or.inl (windowCompression_apply_of_le a b hab x i
      (hi ▸ (show (0 : I) ≤ a i from bot_le)))⟩
  · exact ⟨i, Or.inr (windowCompression_apply_of_ge a b hab x i
      (hi ▸ (show b i ≤ (1 : I) from le_top)))⟩

omit hab in
@[simp] theorem windowCompressionInterpolation_zero (x : N → I) :
    windowCompressionInterpolation a b (0, x) = x := by
  funext i
  change Set.projIcc 0 1 zero_le_one _ = x i
  simp

omit hab in
@[simp] theorem windowCompressionInterpolation_one (x : N → I) :
    windowCompressionInterpolation a b (1, x) = windowCompression a b x := by
  funext i
  change Set.projIcc 0 1 zero_le_one _ = windowCompression a b x i
  simp

/-- The complete compression homotopy preserves every original boundary
face, so postcomposing any based loop gives a relative homotopy. -/
theorem windowCompressionInterpolation_preserves_boundary (s : I) (x : N → I)
    (hx : x ∈ _root_.Cube.boundary N) :
    windowCompressionInterpolation a b (s, x) ∈ _root_.Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := hx
  · have hw := windowCompression_apply_of_le a b hab x i
      (hi ▸ (show (0 : I) ≤ a i from bot_le))
    refine ⟨i, Or.inl ?_⟩
    change Set.projIcc 0 1 zero_le_one
      ((1 - (s : ℝ)) * (x i : ℝ) + (s : ℝ) * windowCompression a b x i) = 0
    rw [hi, hw]
    simp
  · have hw := windowCompression_apply_of_ge a b hab x i
      (hi ▸ (show b i ≤ (1 : I) from le_top))
    refine ⟨i, Or.inr ?_⟩
    change Set.projIcc 0 1 zero_le_one
      ((1 - (s : ℝ)) * (x i : ℝ) + (s : ℝ) * windowCompression a b x i) = 1
    rw [hi, hw]
    simp

end KIP126.Topology.Cube
