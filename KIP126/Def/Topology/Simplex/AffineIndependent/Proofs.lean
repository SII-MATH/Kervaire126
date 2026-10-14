module

public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace KIP126.Topology.Simplex

/-- Injectivity of the actual convex-combination map on the standard
simplex implies affine independence of its vertices. General affine
dependences are shifted into the positive simplex before using injectivity. -/
theorem affineIndependent_of_injective_simplex_sum
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (v : ι → E)
    (hinj : Function.Injective (fun t : stdSimplex ℝ ι => ∑ i, t i • v i)) :
    AffineIndependent ℝ v := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    exact affineIndependent_of_subsingleton ℝ v
  | inr h =>
    letI := h
    rw [affineIndependent_iff_of_fintype]
    intro w hw hv i
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
    let S : ℝ := (∑ i, |w i|) + 1
    have hS : 0 < S := by
      dsimp [S]
      exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => abs_nonneg (w i))) zero_lt_one
    let M : ℝ := (Fintype.card ι : ℝ) * S
    have hM : 0 < M := mul_pos (by exact_mod_cast Fintype.card_pos) hS
    have hpos (i : ι) : 0 ≤ w i + S := by
      have hi : |w i| ≤ ∑ j, |w j| := Finset.single_le_sum
        (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i)
      have hn := neg_abs_le (w i)
      dsimp [S]
      linarith
    have hsum : ∑ i, (w i + S) = M := by
      simp [Finset.sum_add_distrib, hw, M]
    let t : stdSimplex ℝ ι := ⟨fun i => (w i + S) / M,
      fun i => div_nonneg (hpos i) (le_of_lt hM), by
        simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum]
        exact mul_inv_cancel₀ (ne_of_gt hM)⟩
    let s : stdSimplex ℝ ι := ⟨fun _ => S / M,
      fun _ => div_nonneg (le_of_lt hS) (le_of_lt hM), by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc]
        exact div_self (ne_of_gt hM)⟩
    have he : (∑ i, t i • v i) = ∑ i, s i • v i := by
      change (∑ i, ((w i + S) / M) • v i) = ∑ i, (S / M) • v i
      simp only [div_eq_mul_inv, mul_comm _ M⁻¹, mul_smul, ← Finset.smul_sum,
        add_smul, Finset.sum_add_distrib, hv, zero_add]
    have hi := congrArg (fun x : stdSimplex ℝ ι => x i) (hinj he)
    change (w i + S) / M = S / M at hi
    have heq := (div_left_inj' (ne_of_gt hM)).mp hi
    exact add_right_cancel (heq.trans (zero_add S).symm)

end KIP126.Topology.Simplex
