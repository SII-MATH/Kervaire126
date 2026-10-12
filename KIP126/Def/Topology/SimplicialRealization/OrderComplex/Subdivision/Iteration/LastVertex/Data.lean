module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

/-- The actual iterated simplicial last-vertex comparison, with the same
subdivision objects as the actual barycentric homeomorphism. -/
noncomputable def iteratedOrderSubdivisionLastVertex (P : Type u) [PartialOrder P] :
    (n : ℕ) → (nerve (iteratedOrderSubdivision P n) ⟶ nerve P) := fun n => match n with
  | 0 => 𝟙 _
  | n+1 => orderSubdivisionLastVertex (iteratedOrderSubdivision P n) ≫
      iteratedOrderSubdivisionLastVertex P n

end KIP126.Topology.SimplicialRealization
