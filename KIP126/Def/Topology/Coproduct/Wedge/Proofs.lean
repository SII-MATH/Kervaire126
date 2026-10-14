module

public import KIP126.Def.Topology.Coproduct.Wedge.Data
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset

@[expose] public section

namespace KIP126.Topology

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

@[simp] theorem wedgeInclusion_point (j : J) :
    wedgeInclusion X x₀ j (x₀ j) = wedgePoint X x₀ :=
  Quotient.sound (Or.inr ⟨rfl, trivial⟩)

@[simp] theorem wedgeInclusion_eq_point_iff (j : J) (x : X j) :
    wedgeInclusion X x₀ j x = wedgePoint X x₀ ↔ x = x₀ j := by
  constructor
  · intro h
    rcases Quotient.exact h with h | h
    · cases h
    · exact h.1
  · rintro rfl
    exact wedgeInclusion_point j

@[simp] theorem wedgeDesc_inclusion {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (f : ∀ j, C(X j,Y)) (hf : ∀ j, f j (x₀ j) = y₀) (j : J) (x : X j) :
    wedgeDesc X x₀ y₀ f hf (wedgeInclusion X x₀ j x) = f j x := rfl

@[simp] theorem wedgeDesc_point {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (f : ∀ j, C(X j,Y)) (hf : ∀ j, f j (x₀ j) = y₀) :
    wedgeDesc X x₀ y₀ f hf (wedgePoint X x₀) = y₀ := rfl

/-- Equality away from the common point identifies the actual summand. -/
theorem wedgeInclusion_eq_index {i j : J} {x : X i} {y : X j}
    (hx : x ≠ x₀ i) (h : wedgeInclusion X x₀ i x = wedgeInclusion X x₀ j y) : i = j := by
  rcases Quotient.exact h with h | h
  · exact congrArg Sigma.fst (Sum.inl.inj h)
  · exact False.elim (hx h.1)

/-- A selected nonbasepoint in each of any set of distinct summands forms
a closed subset of the actual wedge, provided each summand is T1. -/
theorem wedgeInclusion_selected_isClosed [∀ j, T1Space (X j)]
    (s : Set J) (x : ∀ j, X j) (hx : ∀ j ∈ s, x j ≠ x₀ j) :
    IsClosed ((fun j => wedgeInclusion X x₀ j (x j)) '' s) := by
  classical
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  apply isClosed_sum_iff.mpr
  constructor
  · apply isClosed_sigma_iff.mpr
    intro i
    have he : (fun y : X i => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inl ⟨i,y⟩)) ⁻¹'
        ((fun j => wedgeInclusion X x₀ j (x j)) '' s) =
        if i ∈ s then {x i} else ∅ := by
      ext y
      classical
      by_cases hi : i ∈ s
      · simp only [hi,ite_true,mem_preimage,mem_image,mem_singleton_iff]
        constructor
        · rintro ⟨j,hj,h⟩
          have hji := wedgeInclusion_eq_index (hx j hj) h
          subst j
          rcases Quotient.exact h with h | h
          · exact (eq_of_heq (Sigma.mk.inj (Sum.inl.inj h)).2).symm
          · exact False.elim (hx i hi h.1)
        · rintro rfl
          exact ⟨i,hi,rfl⟩
      · simp only [hi,ite_false,mem_preimage,mem_image,mem_empty_iff_false,iff_false]
        rintro ⟨j,hj,h⟩
        exact hi ((wedgeInclusion_eq_index (hx j hj) h) ▸ hj)
    change IsClosed ((fun y : X i => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inl ⟨i,y⟩)) ⁻¹'
      ((fun j => wedgeInclusion X x₀ j (x j)) '' s))
    rw [he]
    split_ifs <;> simp
  · have he : (fun z : PUnit => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inr z)) ⁻¹'
        ((fun j => wedgeInclusion X x₀ j (x j)) '' s) = ∅ := by
      ext z
      simp only [mem_preimage,mem_image,mem_empty_iff_false,iff_false]
      rintro ⟨j,hj,h⟩
      exact hx j hj ((wedgeInclusion_eq_point_iff j (x j)).mp h)
    change IsClosed ((fun z : PUnit => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inr z)) ⁻¹'
      ((fun j => wedgeInclusion X x₀ j (x j)) '' s))
    rw [he]
    exact isClosed_empty

end KIP126.Topology
