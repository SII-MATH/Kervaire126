module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Dimension.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Proofs
public import KIP126.Def.Topology.Simplex.FiniteFiber.Proofs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Simplex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Initial segments give an actual maximal flag of proper faces of
the standard simplex, with exactly the boundary dimension plus one
vertices. -/
theorem exists_orderProperChains_full_chain (n : ℕ) :
    ∃ c : PartialOrder.NonemptyFiniteChains (orderProperChains (Fin (n + 2))),
      c.finset.card = n + 1 := by
  classical
  let f : Fin (n + 1) → orderProperChains (Fin (n + 2)) := fun i => ⟨{
    finset := Finset.Iic i.castSucc
    nonempty := ⟨i.castSucc, Finset.mem_Iic.mpr le_rfl⟩
    comparable := fun a b => le_total a.val b.val }, by
      change Finset.Iic i.castSucc ≠ Finset.univ
      intro he
      have hc := congrArg Finset.card he
      simp only [Fin.card_Iic, Fin.val_castSucc, Finset.card_univ, Fintype.card_fin] at hc
      omega⟩
  have hf : Monotone f := by
    intro i j hij
    change Finset.Iic i.castSucc ⊆ Finset.Iic j.castSucc
    intro k hk
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hk).trans hij)
  have hi : Function.Injective f := by
    intro i j hij
    have hc := congrArg (fun a : orderProperChains (Fin (n + 2)) => a.val.finset.card) hij
    simp only [f, Fin.card_Iic, Fin.val_castSucc] at hc
    exact Fin.ext (by omega)
  let c : PartialOrder.NonemptyFiniteChains (orderProperChains (Fin (n + 2))) := {
    finset := Finset.univ.image f
    nonempty := ⟨f 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      rcases le_total i j with hij | hji
      · exact Or.inl (hf hij)
      · exact Or.inr (hf hji) }
  refine ⟨c, ?_⟩
  change (Finset.univ.image f).card = n + 1
  rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

/-- In positive sphere dimension there is an actual full-dimensional
boundary point distinct from any specified vertex. This supplies a
regular target value for the proved finite-covering construction. -/
theorem exists_orderBoundary_full_support_point (n : ℕ) (hn : 0 < n)
    [Fintype (orderProperChains (Fin (n + 2)))]
    (p : orderProperChains (Fin (n + 2))) :
    ∃ y : |nerve (orderProperChains (Fin (n + 2)))|,
      (positiveSupport (orderComplexCoordinates _ y)).card = n + 1 ∧
      y ≠ orderVertex _ p := by
  classical
  let Q := orderProperChains (Fin (n + 2))
  obtain ⟨c, hc⟩ := exists_orderProperChains_full_chain n
  obtain ⟨y, hy⟩ := exists_orderOpenStarIntersection_barycenter Q c
  have hs : positiveSupport (orderComplexCoordinates Q y.val) = c.finset := by
    rw [hy]
    ext q
    rw [mem_positiveSupport, orderChainBarycenter_apply]
    by_cases hq : q ∈ c.finset
    · simp only [if_pos hq, hq, iff_true]
      exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr c.nonempty))
    · simp [hq]
  refine ⟨y.val, by rw [hs, hc], ?_⟩
  intro he
  have hv : positiveSupport (orderComplexCoordinates Q (orderVertex Q p)) = {p} := by
    ext q
    rw [mem_positiveSupport, orderComplexCoordinates_vertex]
    by_cases hq : q = p
    · subst q
      simp [stdSimplex.vertex]
    · simp [stdSimplex.vertex, hq, Ne.symm hq]
  have hcard := congrArg Finset.card (hs.symm.trans (he ▸ hv))
  rw [hc, Finset.card_singleton] at hcard
  omega

end KIP126.Topology.SimplicialRealization
