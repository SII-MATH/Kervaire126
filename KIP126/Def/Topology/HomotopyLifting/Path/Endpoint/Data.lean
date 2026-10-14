module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Predicates
public import Mathlib.Topology.CompactOpen

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval

universe u v

/-- A path in the base with specified lifts of its two endpoints. -/
abbrev PathEndpointSpace {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (f : C(E,B)) :=
  {z : (E × E) × C(I,B) // z.2 0 = f z.1.1 ∧ z.2 1 = f z.1.2}

/-- A path gives its actual two endpoints and its image path. -/
def pathEndpointComparison {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (f : C(E,B)) :
    C(C(I,E),PathEndpointSpace f) :=
  ⟨fun p => ⟨((p 0,p 1),f.comp p),rfl,rfl⟩,
    (((continuous_id.eval continuous_const).prodMk
      (continuous_id.eval continuous_const)).prodMk
      (ContinuousMap.continuous_postcomp f)).subtype_mk _⟩

end KIP126.Topology.HomotopyLifting
