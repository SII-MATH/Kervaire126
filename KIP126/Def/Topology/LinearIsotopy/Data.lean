module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.UnitInterval

@[expose] public section

namespace KIP126.Topology

open Matrix
open scoped OnePoint

/-- The actual Euclidean homeomorphism induced by an invertible real
matrix, with the original matrix multiplication as its forward map. -/
noncomputable def invertibleMatrixHomeomorph {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) : (ι → ℝ) ≃ₜ (ι → ℝ) where
  toFun := fun x => A *ᵥ x
  invFun := fun x => A⁻¹ *ᵥ x
  left_inv x := by
    change A⁻¹ *ᵥ (A *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  right_inv x := by
    change A *ᵥ (A⁻¹ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

/-- The same invertible matrix acts on the actual one-point
compactification and fixes its specified point at infinity. -/
noncomputable def onePointMatrixMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    C(OnePoint (ι → ℝ), OnePoint (ι → ℝ)) :=
  ⟨(invertibleMatrixHomeomorph A hA).onePointCongr,
    (invertibleMatrixHomeomorph A hA).onePointCongr.continuous⟩

/-- The actual affine coordinate change, extended to fix infinity. -/
noncomputable def onePointAffineMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) (b : ι → ℝ) :
    C(OnePoint (ι → ℝ), OnePoint (ι → ℝ)) :=
  let e := ((invertibleMatrixHomeomorph A hA).trans (Homeomorph.addRight b)).onePointCongr
  ⟨e, e.continuous⟩

end KIP126.Topology
