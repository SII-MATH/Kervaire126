module

public import KIP126.Def.Topology.SimplicialRealization.Coproduct.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The two disjoint ends, as one actual simplicial subobject of the
order mapping cylinder. -/
def orderMappingCylinderEndsInclusion {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) : simplicialSum (nerve P) (nerve Q) ⟶ nerve (OrderMappingCylinder f) :=
  simplicialSumDesc (orderMappingCylinderSourceInclusion f)
    (orderMappingCylinderTargetInclusion f)

end KIP126.Topology.SimplicialRealization
