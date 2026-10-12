module

public import KIP126.Def.Topology.Simplex.Reindex.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Proofs

@[expose] public section

namespace KIP126.Topology.Simplex
open KIP126.Topology.SimplicialRealization

/-- Reindexing retains the entire coordinate boundary, in both directions. -/
theorem reindexHomeomorph_boundary {P Q : Type*} [Fintype P] [Fintype Q]
    (e : P ≃ Q) (x : stdSimplex ℝ P) :
    (∃ p, x p = 0) ↔ ∃ q, reindexHomeomorph e x q = 0 := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨e p,?_⟩
    change stdSimplex.map e x (e p) = 0
    rw [simplex_map_apply_injective e e.injective]
    exact hp
  · rintro ⟨q,hq⟩
    obtain ⟨p,rfl⟩ := e.surjective q
    refine ⟨p,?_⟩
    change stdSimplex.map e x (e p) = 0 at hq
    rwa [simplex_map_apply_injective e e.injective] at hq

end KIP126.Topology.Simplex
