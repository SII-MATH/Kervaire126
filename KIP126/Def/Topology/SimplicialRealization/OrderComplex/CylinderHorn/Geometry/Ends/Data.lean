module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- Either actual endpoint of the ordered cylinder. -/
def orderCylinderEndEmbedding (P : Type u) [PartialOrder P] (i : Fin 2) :
    P ↪o OrderCylinder P where
  toFun p := (p,i)
  inj' := by intro p q h; exact congrArg Prod.fst h
  map_rel_iff' := by intro p q; change (p ≤ q ∧ i ≤ i) ↔ p ≤ q; simp

def orderCylinderEndInclusion (P : Type u) [PartialOrder P] (i : Fin 2) :
    nerve P ⟶ nerve (OrderCylinder P) :=
  nerveMap (orderCylinderEndEmbedding P i).monotone.functor

end KIP126.Topology.SimplicialRealization
