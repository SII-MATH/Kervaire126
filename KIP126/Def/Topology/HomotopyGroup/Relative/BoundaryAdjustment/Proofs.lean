module

public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Extension.Proofs

@[expose] public section

namespace KIP126.Topology
open Set HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A relative homotopy of the top disk can be incorporated in an
actual cylinder map while retaining the bottom and all side faces. -/
theorem cylinder_top_adjustment {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) (L : C(I × (Fin n → I),Y)) (q : C(Fin n → I,Y))
    (T : (L.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩).HomotopyRel q
      (_root_.Cube.boundary (Fin n))) :
    ∃ A : C(I × (Fin n → I),Y), (∀ x, A (1,x) = q x) ∧
      ∀ z : CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)), A z.val = L z.val := by
  classical
  let B := {z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))}
  let raw : B × I → Y := fun z => if z.1.val.1 = 1 then T (z.2,z.1.val.2) else L z.1.val
  let S₁ : Set (B × I) := {z | z.1.val.1 = 1}
  let Sₕ : Set (B × I) := {z | z.1.val.1 = 0 ∨ z.1.val.2 ∈ _root_.Cube.boundary (Fin n)}
  have h₁ : IsClosed S₁ := isClosed_eq (continuous_subtype_val.comp continuous_fst).fst continuous_const
  have hₕ : IsClosed Sₕ :=
    (isClosed_eq (continuous_subtype_val.comp continuous_fst).fst continuous_const).union
      ((cubeBoundary_isClosed n).preimage (continuous_subtype_val.comp continuous_fst).snd)
  have raw₁ (z : B × I) (hz : z ∈ S₁) : raw z = T (z.2,z.1.val.2) := if_pos hz
  have rawₕ (z : B × I) (hz : z ∈ Sₕ) : raw z = L z.1.val := by
    dsimp only [raw]
    split_ifs with ht
    · rcases hz with h0 | hx
      · exact False.elim (zero_ne_one (h0.symm.trans ht))
      · exact (T.eq_fst z.2 hx).trans (congrArg (fun t => L (t,z.1.val.2)) ht.symm)
    · rfl
  have hc₁ : ContinuousOn raw S₁ :=
    (T.continuous.comp (continuous_snd.prodMk
      (continuous_subtype_val.comp continuous_fst).snd)).continuousOn.congr raw₁
  have hcₕ : ContinuousOn raw Sₕ :=
    (L.continuous.comp (continuous_subtype_val.comp continuous_fst)).continuousOn.congr rawₕ
  have hu : S₁ ∪ Sₕ = univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases z.1.property with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  let K : C(B × I,Y) := ⟨raw,continuousOn_univ.mp
    (hu ▸ hc₁.union_of_isClosed hcₕ h₁ hₕ)⟩
  have hK0 (z : B) : K (z,0) = L z.val := by
    change raw (z,0) = _
    dsimp only [raw]
    split_ifs with ht
    · exact (T.apply_zero z.val.2).trans (congrArg (fun t => L (t,z.val.2)) ht.symm)
    · rfl
  obtain ⟨G,hG0,hGb⟩ := cylinderBoundary_homotopy_extension n L K hK0
  refine ⟨G.comp ⟨fun z => (z,1),continuous_id.prodMk continuous_const⟩,?_,?_⟩
  · intro x
    exact (hGb ⟨(1,x),Or.inr (Or.inl rfl)⟩ 1).trans
      ((raw₁ (⟨(1,x),Or.inr (Or.inl rfl)⟩,1) rfl).trans (T.apply_one x))
  · intro z
    have hb : z.val ∈ cylinderBoundary (_root_.Cube.boundary (Fin n)) :=
      z.property.elim Or.inl (fun h => Or.inr (Or.inr h))
    exact (hGb ⟨z.val,hb⟩ 1).trans (rawₕ (⟨z.val,hb⟩,1) z.property)

end KIP126.Topology
