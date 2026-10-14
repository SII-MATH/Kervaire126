module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.RegularStar.Homeomorph.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open scoped Classical
universe u

/-- The actual full source simplices mapped bijectively on the specified
target simplex vertices. These are the geometric sheets over its interior. -/
def orderFullStarSheets {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q) :=
  {s : PartialOrder.NonemptyFiniteChains P //
    s.finset.card = c.finset.card ∧ s.finset.image f = c.finset}

noncomputable instance orderFullStarSheets_finite {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q) :
    Finite (orderFullStarSheets f c) := by
  letI := finite_nonemptyFiniteChains P
  exact inferInstanceAs (Finite {s : PartialOrder.NonemptyFiniteChains P //
    s.finset.card = c.finset.card ∧ s.finset.image f = c.finset})

instance orderFullStarSheets_topologicalSpace {P Q : Type u}
    [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q) :
    TopologicalSpace (orderFullStarSheets f c) := ⊥

instance orderFullStarSheets_discreteTopology {P Q : Type u}
    [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (c : PartialOrder.NonemptyFiniteChains Q) :
    DiscreteTopology (orderFullStarSheets f c) := ⟨rfl⟩

end KIP126.Topology.SimplicialRealization
