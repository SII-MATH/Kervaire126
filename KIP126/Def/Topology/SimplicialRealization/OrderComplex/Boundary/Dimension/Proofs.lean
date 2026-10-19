module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open scoped Classical
universe u

/-- Strictly nested nonempty proper faces have at most one less vertex
than the ambient finite vertex set. This is the actual dimension bound
for the proper-chain model of the whole simplex boundary. -/
theorem orderChainSizeLE_properChains (P : Type u) [PartialOrder P] [Fintype P] :
    OrderChainSizeLE (orderProperChains P) (Fintype.card P - 1) := by
  classical
  intro c
  have hp (a : c.finset) : 0 < a.val.val.finset.card :=
    Finset.card_pos.mpr a.val.val.nonempty
  have hb (a : c.finset) : a.val.val.finset.card < Fintype.card P := by
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr a.val.property)
  let r : c.finset → Fin (Fintype.card P - 1) := fun a =>
    ⟨a.val.val.finset.card - 1, by have := hp a; have := hb a; omega⟩
  have hr : Function.Injective r := by
    intro a b hab
    have he : a.val.val.finset.card = b.val.val.finset.card := by
      have := congrArg Fin.val hab
      have := hp a
      have := hp b
      dsimp only [r] at *
      omega
    apply Subtype.ext
    apply Subtype.ext
    apply PartialOrder.NonemptyFiniteChains.ext
    obtain h | h := c.comparable a b
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have h := Fintype.card_le_of_injective r hr
  simpa only [Fintype.card_coe, Fintype.card_fin] using h

end KIP126.Topology.SimplicialRealization
