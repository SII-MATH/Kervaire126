module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import KIP126.Def.Topology.LinearIsotopy.Data
public import KIP126.Def.Topology.Compactification.OnePoint.Family.Proofs

@[expose] public section

namespace KIP126.Topology

open Matrix
open scoped unitInterval

/-- Every invertible real matrix admits an actual continuous path of
invertible matrices to a diagonal coordinate-sign matrix. The path is
constructed from Gaussian elimination, straight shear paths and
straight paths of diagonal entries that retain their signs. -/
theorem exists_matrix_path_to_sign_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∃ H : C(I, Matrix ι ι ℝ), H 0 = A ∧ H 1 = Matrix.diagonal ε ∧
        ∀ t, (H t).det ≠ 0 := by
  classical
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A => ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∃ H : C(I, Matrix ι ι ℝ), H 0 = A ∧ H 1 = Matrix.diagonal ε ∧
        ∀ t, (H t).det ≠ 0) A hA ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      simpa only [Matrix.det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]
        using hD
    let ε : ι → ℝ := fun i => if 0 < D i then 1 else -1
    let H : C(I, Matrix ι ι ℝ) :=
      ⟨fun t => Matrix.diagonal (fun i => (1 - (t : ℝ)) * D i + (t : ℝ) * ε i), by
        apply Continuous.matrix_diagonal
        exact continuous_pi (fun _ => by fun_prop)⟩
    refine ⟨ε, fun i => by dsimp [ε]; split_ifs <;> simp, H, ?_, ?_, ?_⟩
    · ext i j
      simp [H]
    · ext i j
      simp [H]
    · intro t
      rw [show H t = Matrix.diagonal (fun i => (1 - (t : ℝ)) * D i + (t : ℝ) * ε i) from rfl,
        Matrix.det_diagonal]
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      have ht0 := t.property.1
      have ht1 := t.property.2
      by_cases ht : (t : ℝ) = 0
      · simpa [ht] using hD' i
      have htpos : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm ht)
      have h1t : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr ht1
      by_cases hi : 0 < D i
      · have hm := mul_nonneg h1t (le_of_lt hi)
        dsimp [ε]
        rw [if_pos hi]
        nlinarith
      · have hi' : D i < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hD' i)
        have hm := mul_nonpos_of_nonneg_of_nonpos h1t (le_of_lt hi')
        dsimp [ε]
        rw [if_neg hi]
        nlinarith
  · intro t
    let H : C(I, Matrix ι ι ℝ) :=
      ⟨fun s => Matrix.transvection t.i t.j ((1 - (s : ℝ)) * t.c), by
        apply continuous_matrix
        intro i j
        simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
        split_ifs <;> fun_prop⟩
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, H, ?_, ?_, ?_⟩
    · simp [H, Matrix.TransvectionStruct.toMatrix]
    · simp [H, Matrix.diagonal_one]
    · intro s
      dsimp [H]
      rw [Matrix.det_transvection_of_ne _ _ t.hij]
      norm_num
  · intro A B hA hB ihA ihB
    obtain ⟨ε, hε, H, H0, H1, Hdet⟩ := ihA
    obtain ⟨η, hη, K, K0, K1, Kdet⟩ := ihB
    refine ⟨fun i => ε i * η i, ?_, ⟨fun t => H t * K t,
      H.continuous.matrix_mul K.continuous⟩, ?_, ?_, ?_⟩
    · intro i
      rcases hε i with he | he <;> rcases hη i with he' | he' <;> simp [he, he']
    · change H 0 * K 0 = _
      rw [H0, K0]
    · change H 1 * K 1 = _
      rw [H1, K1, Matrix.diagonal_mul_diagonal]
    · intro t
      change (H t * K t).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (Hdet t) (Kdet t)

end KIP126.Topology
