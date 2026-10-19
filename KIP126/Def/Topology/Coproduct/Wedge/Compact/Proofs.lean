module

public import KIP126.Def.Topology.Coproduct.Wedge.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

/-- Nonbasepoints selected in distinct summands form an actual discrete
subset of the quotient wedge. -/
theorem wedgeInclusion_selected_isDiscrete [∀ j, T1Space (X j)]
    (s : Set J) (x : ∀ j, X j) (hx : ∀ j ∈ s, x j ≠ x₀ j) :
    IsDiscrete ((fun j => wedgeInclusion X x₀ j (x j)) '' s) := by
  apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
  intro t ht
  let s' := {j | j ∈ s ∧ wedgeInclusion X x₀ j (x j) ∈ t}
  have he : (fun j => wedgeInclusion X x₀ j (x j)) '' s' = t := by
    apply Set.Subset.antisymm
    · rintro _ ⟨j,hj,rfl⟩
      exact hj.2
    · intro z hz
      obtain ⟨j,hj,rfl⟩ := ht hz
      exact ⟨j,⟨hj,hz⟩,rfl⟩
  refine ⟨t,?_,Set.inter_eq_left.mpr ht⟩
  rw [← he]
  exact wedgeInclusion_selected_isClosed s' x (fun j hj => hx j hj.1)

/-- A compact subset of the actual wedge meets only finitely many
summands away from the common basepoint. The T1 hypothesis is on the
original summands, and no local finiteness assumption is imposed. -/
theorem isCompact_wedge_finite_support [∀ j, T1Space (X j)]
    {K : Set (Wedge X x₀)} (hK : IsCompact K) :
    {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ K}.Finite := by
  classical
  let s : Set J := {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ K}
  let x (j : J) : X j := if h : j ∈ s then h.choose else x₀ j
  have hx (j : J) (hj : j ∈ s) : x j ≠ x₀ j ∧ wedgeInclusion X x₀ j (x j) ∈ K := by
    dsimp only [x]
    rw [dif_pos hj]
    exact hj.choose_spec
  let f (j : J) := wedgeInclusion X x₀ j (x j)
  have hclosed : IsClosed (f '' s) :=
    wedgeInclusion_selected_isClosed s x (fun j hj => (hx j hj).1)
  have hdisc : IsDiscrete (f '' s) :=
    wedgeInclusion_selected_isDiscrete s x (fun j hj => (hx j hj).1)
  have hsub : f '' s ⊆ K := by
    rintro _ ⟨j,hj,rfl⟩
    exact (hx j hj).2
  have hinj : Set.InjOn f s := fun i hi j _ hij =>
    wedgeInclusion_eq_index (hx i hi).1 hij
  exact ((hK.of_isClosed_subset hclosed hsub).finite hdisc).of_finite_image hinj

/-- Every continuous map from a compact space into the actual wedge has
only finitely many nonbasepoint summands in its image. -/
theorem continuousMap_wedge_finite_support [∀ j, T1Space (X j)]
    {A : Type*} [TopologicalSpace A] [CompactSpace A] (f : C(A,Wedge X x₀)) :
    {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ Set.range f}.Finite :=
  isCompact_wedge_finite_support (isCompact_range f.continuous)

end KIP126.Topology
