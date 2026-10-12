module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.RegularStar.Homeomorph.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Simplex.Proofs
public import KIP126.Def.Topology.Simplex.Interior.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false

/-- A full-dimensional common open star in the actual finite order
complex is Euclidean space of dimension one less than its chain size. -/
theorem exists_orderFullStar_homeomorph_euclidean
    (P : Type u) [PartialOrder P] [Fintype P] (n : ℕ)
    (hP : OrderChainSizeLE P (n + 1))
    (c : PartialOrder.NonemptyFiniteChains P) (hc : c.finset.card = n + 1) :
    Nonempty (orderOpenStarIntersection P c.finset ≃ₜ (Fin n → ℝ)) := by
  letI : Nonempty c.finset := c.nonempty.to_subtype
  letI : LinearOrder c.finset := {
    le_total := fun a b => c.comparable a b
    toDecidableLE := inferInstance }
  have hcard : Fintype.card c.finset = n + 1 := (Fintype.card_coe _).trans hc
  let d : PartialOrder.NonemptyFiniteChains c.finset := {
    finset := Finset.univ
    nonempty := Finset.univ_nonempty
    comparable := fun a b => le_total a.val b.val }
  let inclusion : c.finset →o P := ⟨Subtype.val, fun _ _ h => h⟩
  have hbound : OrderChainSizeLE c.finset (n + 1) := by
    intro s
    exact (Finset.card_le_card (Finset.subset_univ s.finset)).trans_eq
      ((Finset.card_univ).trans hcard)
  have hd : d.finset.card = n + 1 := by simpa [d] using hcard
  have himage : d.finset.image inclusion = c.finset := by
    ext p
    simp only [d, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  obtain ⟨h, _⟩ := exists_orderMap_full_star_homeomorph inclusion (n + 1)
    hbound hP d hd Subtype.val_injective.injOn
  let hstar : orderOpenStarIntersection c.finset d.finset ≃ₜ
      orderOpenStarIntersection P c.finset :=
    h.trans (Homeomorph.setCongr (congrArg (orderOpenStarIntersection P) himage))
  obtain ⟨e, he⟩ := exists_linearOrderCoordinates_homeomorph c.finset
  have hi (x : |nerve c.finset|) :
      x ∈ orderOpenStarIntersection c.finset d.finset ↔ ∀ a, 0 < e x a := by
    rw [he]
    simp only [orderOpenStarIntersection, orderOpenStar, Set.mem_setOf_eq, d,
      Finset.mem_univ, forall_const]
  obtain ⟨a⟩ := exists_stdSimplex_positive_homeomorph_of_card n hcard
  exact ⟨hstar.symm.trans ((e.subtype hi).trans a)⟩

end KIP126.Topology.SimplicialRealization
