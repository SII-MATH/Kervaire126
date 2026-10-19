module

public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

namespace KIP126.Topology

/-- Precomposition transports a relative homotopy along a continuous
map that takes the new fixed region into the old one. -/
theorem homotopicRel_precomp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f g : C(X,Y)} {S : Set X} (h : f.HomotopicRel g S)
    (a : C(Z,X)) {T : Set Z} (ha : Set.MapsTo a T S) :
    (f.comp a).HomotopicRel (g.comp a) T := by
  obtain ⟨H⟩ := h
  exact ⟨{
    toFun := fun z => H (z.1,a z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk (a.continuous.comp continuous_snd))
    map_zero_left := fun z => H.apply_zero (a z)
    map_one_left := fun z => H.apply_one (a z)
    prop' := fun t z hz => H.eq_fst t (ha hz) }⟩

end KIP126.Topology
