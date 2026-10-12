module

public import KIP126.Def.Topology.Collapse.Map.Data

@[expose] public section

namespace KIP126.Topology

@[simp] theorem collapsePreimageMap_mk
    {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    (f : C(E, Y)) (S : Set Y) (x : E) :
    collapsePreimageMap f S (Quot.mk _ x) = Quot.mk _ (f x) := rfl

end KIP126.Topology
