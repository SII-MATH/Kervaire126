module

public import KIP126.Def.Topology.Coproduct.Wedge.Subfamily.Data
public import KIP126.Def.Topology.Coproduct.Wedge.Compact.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

@[simp] theorem wedgeSubfamilyInclusion_point (s : Set J) :
    wedgeSubfamilyInclusion X x₀ s (wedgePoint _ _) = wedgePoint X x₀ := rfl

@[simp] theorem wedgeSubfamilyRetraction_point (s : Set J) :
    wedgeSubfamilyRetraction X x₀ s (wedgePoint X x₀) = wedgePoint _ _ := rfl

@[simp] theorem wedgeSubfamilyInclusion_inclusion (s : Set J) (j : s) (x : X j.val) :
    wedgeSubfamilyInclusion X x₀ s (wedgeInclusion _ _ j x) =
      wedgeInclusion X x₀ j.val x := rfl

@[simp] theorem wedgeSubfamilyRetraction_inclusion (s : Set J) (j : J)
    (hj : j ∈ s) (x : X j) :
    wedgeSubfamilyRetraction X x₀ s (wedgeInclusion X x₀ j x) =
      wedgeInclusion (fun j : s => X j.val) (fun j => x₀ j.val) ⟨j,hj⟩ x := by
  classical
  simp only [wedgeSubfamilyRetraction,wedgeDesc_inclusion,dif_pos hj]

/-- The displayed subfamily projection really retracts the actual
inclusion, including at the common point. -/
theorem wedgeSubfamilyRetraction_leftInverse (s : Set J) :
    Function.LeftInverse (wedgeSubfamilyRetraction X x₀ s)
      (wedgeSubfamilyInclusion X x₀ s) := by
  intro z
  refine Quotient.inductionOn z ?_
  rintro (⟨j,x⟩ | ⟨⟩)
  · exact wedgeSubfamilyRetraction_inclusion s j.val j.property x
  · rfl

/-- An inclusion followed by the actual subfamily retraction fixes every
point whose nonbasepoint summand belongs to the selected subfamily. -/
theorem wedgeSubfamilyInclusion_retraction_of_support (s : Set J) (z : Wedge X x₀)
    (hz : ∀ j (x : X j), x ≠ x₀ j → wedgeInclusion X x₀ j x = z → j ∈ s) :
    wedgeSubfamilyInclusion X x₀ s (wedgeSubfamilyRetraction X x₀ s z) = z := by
  classical
  induction z using Quotient.inductionOn with
  | h z =>
    rcases z with ⟨j,x⟩ | ⟨⟩
    · change wedgeSubfamilyInclusion X x₀ s
        (wedgeSubfamilyRetraction X x₀ s (wedgeInclusion X x₀ j x)) = wedgeInclusion X x₀ j x
      by_cases hx : x = x₀ j
      · subst x
        simp
      · rw [wedgeSubfamilyRetraction_inclusion s j (hz j x hx rfl)]
        rfl
    · rfl

/-- Every continuous compact-domain map into the actual wedge factors
continuously through the wedge of finitely many of the same summands. -/
theorem continuousMap_wedge_factor_finite [∀ j, T1Space (X j)]
    {A : Type*} [TopologicalSpace A] [CompactSpace A] (f : C(A,Wedge X x₀)) :
    ∃ (s : Finset J)
      (g : C(A,Wedge (fun j : (s : Set J) => X j.val) (fun j => x₀ j.val))),
      (wedgeSubfamilyInclusion X x₀ (s : Set J)).comp g = f := by
  classical
  let support := {j | ∃ x : X j, x ≠ x₀ j ∧ wedgeInclusion X x₀ j x ∈ Set.range f}
  have hs : support.Finite := continuousMap_wedge_finite_support f
  let s := hs.toFinset
  refine ⟨s,(wedgeSubfamilyRetraction X x₀ (s : Set J)).comp f,?_⟩
  apply ContinuousMap.ext
  intro a
  apply wedgeSubfamilyInclusion_retraction_of_support
  intro j x hx he
  change j ∈ hs.toFinset
  exact hs.mem_toFinset.mpr ⟨x,hx,⟨a,he.symm⟩⟩

end KIP126.Topology
