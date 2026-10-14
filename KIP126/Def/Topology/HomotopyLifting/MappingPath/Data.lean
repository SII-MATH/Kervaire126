module

public import KIP126.Def.Topology.HomotopyLifting.Predicates

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v

/-- The actual mapping-path total space, with its initial endpoint fixed
by the original map and its final endpoint free. -/
abbrev MappingPathSpace {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) := {z : X × C(I,Y) // z.2 0 = f z.1}

/-- Evaluate the retained path at its free endpoint. -/
def mappingPathEndpoint {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) : C(MappingPathSpace f,Y) :=
  ⟨fun z => z.val.2 1,continuous_subtype_val.snd.eval continuous_const⟩

end KIP126.Topology.HomotopyLifting
