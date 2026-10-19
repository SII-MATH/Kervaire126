module

public import KIP126.Def.Topology.SimplicialRealization.Product.Weak.Proofs
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Simplicial Topology
open scoped unitInterval Topology.Homotopy
universe u
set_option backward.isDefEq.respectTransparency false

/-- Product comparison reflects all relative homotopies with compact
parameter space, by lifting the actual homotopy continuously. -/
theorem productComparison_homotopicRel_iff (X Y : SSet.{u})
    {D : Type*} [TopologicalSpace D] [CompactSpace D]
    (a b : C(D,|X ⊗ Y|)) (S : Set D) :
    (productComparison X Y |>.comp a).HomotopicRel
        (productComparison X Y |>.comp b) S ↔ a.HomotopicRel b S := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨h,hh⟩ := continuousMap_lift_productComparison X Y H.toContinuousMap
    have hinj : Function.Injective (productComparison X Y) :=
      (productComparison_bijective X Y).1
    exact ⟨{
      toContinuousMap := h
      map_zero_left := fun x => hinj ((hh (0,x)).trans (H.apply_zero x))
      map_one_left := fun x => hinj ((hh (1,x)).trans (H.apply_one x))
      prop' := fun t x hx => hinj ((hh (t,x)).trans (H.eq_fst t hx)) }⟩
  · exact fun H => H.comp_continuousMap (productComparison X Y)

/-- Every based cubical loop in a product of realizations has an exact
based lift to the realization of the simplicial product. -/
theorem genLoop_lift_productComparison (X Y : SSet.{u})
    (c : |X ⊗ Y|) (r : ℕ)
    (p : GenLoop (Fin r) (|X| × |Y|) (productComparison X Y c)) :
    ∃ q : GenLoop (Fin r) |X ⊗ Y| c,
      (productComparison X Y).comp q.val = p.val := by
  obtain ⟨q,hq⟩ := continuousMap_lift_productComparison X Y p.val
  have hbase (x : Fin r → I) (hx : x ∈ Cube.boundary (Fin r)) : q x = c :=
    (productComparison_bijective X Y).1 ((hq x).trans (p.property x hx))
  exact ⟨⟨q,hbase⟩,ContinuousMap.ext hq⟩

end KIP126.Topology.SimplicialRealization
