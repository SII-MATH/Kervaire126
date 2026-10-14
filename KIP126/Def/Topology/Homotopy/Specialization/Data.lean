module

public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v

/-- A pointwise specialization gives an actual homotopy, fixed on the
entire equalizer. Before the final time it is `f`; at the final time it
is `g`. Continuity follows from the stated inclusion of open preimages. -/
noncomputable def homotopyRelOfOpenPreimageSubset
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (f g : C(A,B))
    (h : ∀ U : Set B, IsOpen U → g ⁻¹' U ⊆ f ⁻¹' U) :
    f.HomotopyRel g {x | f x = g x} := by
  classical
  refine { toFun := fun tx => if tx.1 = 1 then g tx.2 else f tx.2
           continuous_toFun := ?_
           map_zero_left := ?_
           map_one_left := ?_
           prop' := ?_ }
  · apply continuous_def.mpr
    intro U hU
    have he : (fun tx : I × A => if tx.1 = 1 then g tx.2 else f tx.2) ⁻¹' U =
        (({1} : Set I)ᶜ ×ˢ (f ⁻¹' U)) ∪ (Set.univ ×ˢ (g ⁻¹' U)) := by
      ext tx
      by_cases ht : tx.1 = 1
      · simp [ht]
      · simp only [ht,ite_false,Set.mem_preimage,Set.mem_union,Set.mem_prod,
          Set.mem_compl_iff,Set.mem_singleton_iff,not_false_eq_true,true_and,
          Set.mem_univ]
        constructor
        · exact Or.inl
        · rintro (hf | hg)
          · exact hf
          · exact h U hU hg
    rw [he]
    exact (isClosed_singleton.isOpen_compl.prod (hU.preimage f.continuous)).union
      (isOpen_univ.prod (hU.preimage g.continuous))
  · intro x
    simp
  · intro x
    simp
  · intro t x hx
    change (if t = 1 then g x else f x) = f x
    split_ifs
    · exact hx.symm
    · rfl

end KIP126.Topology
