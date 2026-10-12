module

public import KIP126.Def.Topology.Coproduct.Wedge.HomotopySupport.Proofs
public import KIP126.Def.Topology.Homotopy.Specialization.Data

@[expose] public section

namespace KIP126.Topology

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

/-- Discarding summands whose image points lie in their basepoint
neighborhood kernels gives a homotopy relative to every point already
fixed by the actual subfamily retraction. -/
theorem continuousMap_wedge_homotopy_of_distinguishable_support
    {A : Type*} [TopologicalSpace A] (s : Set J) (f : C(A,Wedge X x₀))
    (hs : ∀ j (x : X j), x ∉ basepointNeighborhoodKernel (x₀ j) →
      wedgeInclusion X x₀ j x ∈ Set.range f → j ∈ s) :
    let g := ((wedgeSubfamilyInclusion X x₀ s).comp
      (wedgeSubfamilyRetraction X x₀ s)).comp f
    Nonempty (f.HomotopyRel g {a | f a = g a}) :=
  ⟨homotopyRelOfOpenPreimageSubset f _
    (wedgeSubfamilyRetraction_comp_preimage_subset s f hs)⟩

/-- A compact-domain map into an arbitrary actual wedge is homotopic
to its actual finite-subfamily retraction followed by inclusion. The
homotopy fixes all points where that retraction is already the identity,
in particular the entire based boundary of a based cubical map.
No T1, compact-generation, or well-basedness hypothesis is used. -/
theorem continuousMap_wedge_homotopy_finite_support
    {A : Type*} [TopologicalSpace A] [CompactSpace A] (f : C(A,Wedge X x₀)) :
    ∃ s : Finset J,
      let g := ((wedgeSubfamilyInclusion X x₀ (s : Set J)).comp
        (wedgeSubfamilyRetraction X x₀ (s : Set J))).comp f
      Nonempty (f.HomotopyRel g {a | f a = g a}) := by
  classical
  have hs := continuousMap_wedge_finite_distinguishable_support f
  refine ⟨hs.toFinset,continuousMap_wedge_homotopy_of_distinguishable_support _ f ?_⟩
  intro j x hx hxf
  exact hs.mem_toFinset.mpr ⟨x,hx,hxf⟩

end KIP126.Topology
