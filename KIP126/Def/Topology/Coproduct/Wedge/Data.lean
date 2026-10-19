module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace KIP126.Topology

universe u v

variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)] (x₀ : ∀ j, X j)

/-- The actual disjoint union with one extra common basepoint. This also
specifies the empty wedge without a nonemptiness hypothesis on the index. -/
abbrev WedgeCarrier := (Σ j, X j) ⊕ PUnit

/-- Exactly the original basepoints and the extra point are collapsed. -/
def WedgeCollapsed : WedgeCarrier X → Prop
  | Sum.inl ⟨j,x⟩ => x = x₀ j
  | Sum.inr _ => True

/-- The equivalence relation for the actual wedge topology. -/
def wedgeSetoid : Setoid (WedgeCarrier X) where
  r a b := a = b ∨ (WedgeCollapsed X x₀ a ∧ WedgeCollapsed X x₀ b)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    trans := by
      intro a b c h k
      rcases h with rfl | ⟨ha,hb⟩
      · exact k
      rcases k with rfl | ⟨_,hc⟩
      · exact Or.inr ⟨ha,hb⟩
      · exact Or.inr ⟨ha,hc⟩ }

/-- The wedge has the genuine quotient topology of its disjoint union. -/
abbrev Wedge := Quotient (wedgeSetoid X x₀)

def wedgePoint : Wedge X x₀ := Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inr PUnit.unit)

def wedgeInclusion (j : J) : C(X j,Wedge X x₀) :=
  ⟨fun x => Quotient.mk' (s := wedgeSetoid X x₀) (Sum.inl ⟨j,x⟩),
    continuous_quotient_mk'.comp (continuous_inl.comp continuous_sigmaMk)⟩

/-- Compatible continuous maps descend through the actual common-point
quotient. -/
def wedgeDesc {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (f : ∀ j, C(X j,Y)) (hf : ∀ j, f j (x₀ j) = y₀) : C(Wedge X x₀,Y) := by
  let g : WedgeCarrier X → Y := Sum.elim (fun z => f z.1 z.2) (fun _ => y₀)
  have hpoint (z : WedgeCarrier X) (hz : WedgeCollapsed X x₀ z) : g z = y₀ := by
    cases z with
    | inl z => rcases z with ⟨j,x⟩; change x = x₀ j at hz; subst x; exact hf j
    | inr _ => rfl
  have hr : ∀ a b, (wedgeSetoid X x₀).r a b → g a = g b := by
    intro a b h
    rcases h with rfl | ⟨ha,hb⟩
    · rfl
    · exact (hpoint a ha).trans (hpoint b hb).symm
  exact ⟨Quotient.lift g hr,
    (continuous_sum_dom.mpr
      ⟨continuous_sigma (fun j => (f j).continuous),continuous_const⟩).quotient_lift hr⟩

end KIP126.Topology
