module

public import KIP126.Def.Topology.FiberBundle.Pullback.Chart.Data
public import KIP126.Def.Topology.FiberBundle.Chart.Proofs
public import KIP126.Def.Topology.FiberBundle.Pullback.Proofs

@[expose] public section

namespace KIP126.Topology

variable {E A B F : Type*} [TopologicalSpace E] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace F]
set_option backward.isDefEq.respectTransparency false

@[simp] theorem pullbackChartHomeomorph_fst (p : C(E,B)) (a : C(A,B))
    (T : Bundle.Trivialization F p) (z : pullbackSndMap p a ⁻¹' (a ⁻¹' T.baseSet)) :
    (pullbackChartHomeomorph p a T z).1.val = z.val.val.2 := rfl

/-- Pulling back actual local charts along a continuous base map preserves
local triviality for the literal topological fiber product. -/
theorem localTriviality_pullback [Nonempty F] (p : C(E,B)) (a : C(A,B))
    (hp : ∀ b, ∃ T : Bundle.Trivialization F p, b ∈ T.baseSet) :
    ∀ x, ∃ T : Bundle.Trivialization F (pullbackSndMap p a), x ∈ T.baseSet := by
  intro x
  obtain ⟨T,hT⟩ := hp (a x)
  obtain ⟨T',_,hT'⟩ := FiberBundle.exists_trivialization_at_of_open_product
    (pullbackSndMap p a) (a ⁻¹' T.baseSet) (T.open_baseSet.preimage a.continuous)
    (pullbackChartHomeomorph p a T) (fun _ => rfl) x hT
  exact ⟨T',hT'⟩

end KIP126.Topology
