module

public import KIP126.Def.Topology.FiberBundle.Chart.Global.Data

@[expose] public section

namespace KIP126.Topology.FiberBundle

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- Global product coordinates give a local chart at every actual base point. -/
theorem localTriviality_of_globalProduct (p : C(E,B)) (e : E ≃ₜ B × F)
    (he : ∀ x, (e x).1 = p x) :
    ∀ b, ∃ T : Bundle.Trivialization F p, b ∈ T.baseSet :=
  fun _ => ⟨trivializationOfGlobalProduct p e he,Set.mem_univ _⟩

end KIP126.Topology.FiberBundle
