module

public import KIP126.Def.Topology.LinearIsotopy.Proofs

@[expose] public section

namespace KIP126.Topology

open Matrix
open scoped unitInterval OnePoint

/-- An actual continuous path through invertible matrices gives an
actual homotopy on their one-point compactifications, fixed at infinity. -/
theorem onePointMatrixMap_homotopic_of_matrix_path
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (H : C(I, Matrix ι ι ℝ)) (h0 : H 0 = A) (h1 : H 1 = B)
    (hdet : ∀ t, (H t).det ≠ 0) :
    Nonempty (ContinuousMap.HomotopyRel (onePointMatrixMap A hA)
      (onePointMatrixMap B hB) {∞}) := by
  have hinv : Continuous (fun t => (H t)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuousAt_matrix_inv (H t) ?_).comp H.continuous.continuousAt
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hdet t)
  have hc : Continuous (fun z : I × OnePoint (ι → ℝ) =>
      OnePoint.map (fun x => H z.1 *ᵥ x) z.2) := by
    apply continuous_onePoint_map_family_of_inverse
      (fun z : I × (ι → ℝ) => H z.1 *ᵥ z.2)
      (fun z : I × (ι → ℝ) => (H z.1)⁻¹ *ᵥ z.2)
      ((H.continuous.comp continuous_fst).matrix_mulVec continuous_snd)
      ((hinv.comp continuous_fst).matrix_mulVec continuous_snd)
    intro t x
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet t)), Matrix.one_mulVec]
  refine ⟨{
    toFun := fun z => OnePoint.map (fun x => H z.1 *ᵥ x) z.2
    continuous_toFun := hc
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    change OnePoint.map (fun x => H 0 *ᵥ x) x = OnePoint.map (fun x => A *ᵥ x) x
    rw [h0]
  · intro x
    change OnePoint.map (fun x => H 1 *ᵥ x) x = OnePoint.map (fun x => B *ᵥ x) x
    rw [h1]
  · intro t x hx
    have hx' : x = ∞ := Set.mem_singleton_iff.mp hx
    subst x
    rfl

/-- Every actual invertible linear coordinate change on real affine
space is homotopic after one-point compactification to a coordinate-sign
map, through a homotopy fixing infinity. No degree classification is used. -/
theorem exists_onePointMatrixMap_homotopy_sign_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∃ hε : (Matrix.diagonal ε).det ≠ 0,
        Nonempty (ContinuousMap.HomotopyRel (onePointMatrixMap A hA)
          (onePointMatrixMap (Matrix.diagonal ε) hε) {∞}) := by
  obtain ⟨ε, hε, H, h0, h1, hdet⟩ := exists_matrix_path_to_sign_diagonal A hA
  have he : (Matrix.diagonal ε).det ≠ 0 := h1 ▸ hdet 1
  exact ⟨ε, hε, he, onePointMatrixMap_homotopic_of_matrix_path A _ hA he H h0 h1 hdet⟩

/-- Translation of actual affine coordinates disappears through a
genuine homotopy of their compactifications, fixed at infinity. -/
theorem onePointAffineMap_homotopic_linear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) (b : ι → ℝ) :
    Nonempty (ContinuousMap.HomotopyRel (onePointAffineMap A hA b)
      (onePointMatrixMap A hA) {∞}) := by
  let f : I × (ι → ℝ) → (ι → ℝ) := fun z => A *ᵥ z.2 + (1 - (z.1 : ℝ)) • b
  let g : I × (ι → ℝ) → (ι → ℝ) := fun z => A⁻¹ *ᵥ (z.2 - (1 - (z.1 : ℝ)) • b)
  have hf : Continuous f := by
    exact (continuous_const.matrix_mulVec continuous_snd).add (by fun_prop)
  have hg : Continuous g := continuous_const.matrix_mulVec (by fun_prop)
  have hgf : ∀ t x, g (t, f (t, x)) = x := by
    intro t x
    dsimp [f, g]
    rw [add_sub_cancel_right, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  refine ⟨{
    toFun := fun z => OnePoint.map (fun x => f (z.1, x)) z.2
    continuous_toFun := continuous_onePoint_map_family_of_inverse f g hf hg hgf
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    induction x using OnePoint.rec with
    | infty => rfl
    | coe x => change (f (0, x) : OnePoint (ι → ℝ)) = ↑(A *ᵥ x + b); simp [f]
  · intro x
    induction x using OnePoint.rec with
    | infty => rfl
    | coe x => change (f (1, x) : OnePoint (ι → ℝ)) = ↑(A *ᵥ x); simp [f]
  · intro t x hx
    have hx' : x = ∞ := Set.mem_singleton_iff.mp hx
    subst x
    rfl

/-- Every invertible affine coordinate change has the same based
homotopy class on its one-point compactification as an actual diagonal
coordinate-sign map. -/
theorem exists_onePointAffineMap_homotopy_sign_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) (b : ι → ℝ) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∃ hε : (Matrix.diagonal ε).det ≠ 0,
        Nonempty (ContinuousMap.HomotopyRel (onePointAffineMap A hA b)
          (onePointMatrixMap (Matrix.diagonal ε) hε) {∞}) := by
  obtain ⟨ε, hε, hd, H⟩ := exists_onePointMatrixMap_homotopy_sign_diagonal A hA
  exact ⟨ε, hε, hd, ⟨(onePointAffineMap_homotopic_linear A hA b).some.trans H.some⟩⟩

end KIP126.Topology
