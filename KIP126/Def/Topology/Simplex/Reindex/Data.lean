module

public import Mathlib.Analysis.Convex.StdSimplex

@[expose] public section

namespace KIP126.Topology.Simplex

/-- Reindexing the original simplex coordinates is an actual
homeomorphism, including when the finite indexing universes differ. -/
noncomputable def reindexHomeomorph {P Q : Type*} [Fintype P] [Fintype Q]
    (e : P ≃ Q) : stdSimplex ℝ P ≃ₜ stdSimplex ℝ Q where
  toFun := stdSimplex.map e
  invFun := stdSimplex.map e.symm
  left_inv x := by
    rw [stdSimplex.map_comp_apply]
    have h : (e.symm : Q → P) ∘ e = id := funext e.symm_apply_apply
    rw [h,stdSimplex.map_id_apply]
  right_inv x := by
    rw [stdSimplex.map_comp_apply]
    have h : (e : P → Q) ∘ e.symm = id := funext e.apply_symm_apply
    rw [h,stdSimplex.map_id_apply]
  continuous_toFun := stdSimplex.continuous_map e
  continuous_invFun := stdSimplex.continuous_map e.symm

end KIP126.Topology.Simplex
