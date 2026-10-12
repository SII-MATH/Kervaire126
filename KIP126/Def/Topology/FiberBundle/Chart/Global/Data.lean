module

public import KIP126.Def.Topology.FiberBundle.Chart.Data

@[expose] public section

namespace KIP126.Topology.FiberBundle

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- A global product homeomorphism is an actual bundle trivialization
over the whole base, without any choice of values outside a chart. -/
def trivializationOfGlobalProduct (p : C(E,B)) (e : E ≃ₜ B × F)
    (he : ∀ x, (e x).1 = p x) : Bundle.Trivialization F p where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun := fun x _ => he x

end KIP126.Topology.FiberBundle
