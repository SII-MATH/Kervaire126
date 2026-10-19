module

public import KIP126.Def.Topology.Simplex.Homotopy.Proofs
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.AlgebraicTopology.TopologicalSimplex

@[expose] public section

namespace KIP126.Topology.Simplex

open CategoryTheory
open scoped unitInterval

/-- The actual affine time coordinate of a triangle, with times zero,
one half and one at its three vertices. -/
noncomputable def triangleTime : C(stdSimplex ℝ (Fin 3),I) where
  toFun s := ⟨s 1 / 2 + s 2, by
    constructor
    · exact add_nonneg (div_nonneg (s.property.1 1) (by norm_num)) (s.property.1 2)
    · have h := stdSimplex.sum_eq_one s
      simp only [Fin.sum_univ_three] at h
      have h₀ : 0 ≤ s 0 := s.property.1 0
      have h₁ : 0 ≤ s 1 := s.property.1 1
      linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply 1).comp continuous_subtype_val).div_const 2 |>.add
      ((continuous_apply 2).comp continuous_subtype_val)

/-- The actual edge opposite a specified vertex of the ordinary triangle. -/
noncomputable def triangleEdge (i : Fin 3) : C(I,stdSimplex ℝ (Fin 3)) :=
  ⟨fun t => stdSimplex.map (SimplexCategory.δ i).toOrderHom
    (stdSimplexHomeomorphUnitInterval.symm t),
      (stdSimplex.continuous_map _).comp stdSimplexHomeomorphUnitInterval.symm.continuous⟩

end KIP126.Topology.Simplex
