module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped Classical

universe u

/-- The singleton chain associated to an original vertex. -/
def orderSingletonChain {P : Type u} [PartialOrder P] (p : P) :
    PartialOrder.NonemptyFiniteChains P where
  finset := {p}
  nonempty := Finset.singleton_nonempty p
  comparable := by
    rintro ⟨q,hq⟩ ⟨r,hr⟩
    simp only [Finset.mem_singleton] at hq hr
    exact Or.inl (show q ≤ r from le_of_eq (hq.trans hr.symm))

/-- Repeated singleton chains keep track of the same actual original
vertex through every finite subdivision. -/
def iteratedOrderSubdivisionVertex (P : Type u) [PartialOrder P] :
    (n : ℕ) → P → iteratedOrderSubdivision P n := fun n => match n with
  | 0 => id
  | n+1 => fun p => orderSingletonChain (iteratedOrderSubdivisionVertex P n p)

end KIP126.Topology.SimplicialRealization
