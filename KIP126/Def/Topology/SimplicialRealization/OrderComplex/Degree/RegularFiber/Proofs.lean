module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Proofs
public import KIP126.Def.Topology.Simplex.FiniteFiber.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open Simplex
universe u

/-- An actual realization point is supported on no more vertices than
the specified dimension bound on the order complex. -/
theorem orderComplexCoordinates_positiveSupport_card_le
    (P : Type u) [PartialOrder P] [Fintype P] (N : ℕ)
    (hP : OrderChainSizeLE P N) (x : |nerve P|) :
    (positiveSupport (orderComplexCoordinates P x)).card ≤ N := by
  let c : PartialOrder.NonemptyFiniteChains P := {
    finset := positiveSupport (orderComplexCoordinates P x)
    nonempty := by
      obtain ⟨p, hp⟩ := simplex_exists_positive (orderComplexCoordinates P x)
      exact ⟨p, (mem_positiveSupport _ _).mpr hp⟩
    comparable := fun p q => orderComplexCoordinates_hasChainSupport P x p.val q.val
      ((mem_positiveSupport _ _).mp p.property) ((mem_positiveSupport _ _).mp q.property) }
  exact hP c

/-- The actual realization of a monotone map has finite fiber over every
point with as many positive coordinates as the source chain-size bound.
These are the full-dimensional simplex interior points used for counting
local contributions to a piecewise-linear degree. -/
theorem finite_orderMap_fiber_of_full_support {P Q : Type u}
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N) (y : |nerve Q|)
    (hy : (positiveSupport (orderComplexCoordinates Q y)).card = N) :
    Finite {x : |nerve P| // SSet.toTop.map (nerveMap f.monotone.functor) x = y} := by
  let E := {x : stdSimplex ℝ P // (positiveSupport x).card ≤ N ∧
    stdSimplex.map f x = orderComplexCoordinates Q y}
  letI : Finite E := finite_fiber_of_positiveSupport_card f (orderComplexCoordinates Q y) N hy
  let e : {x : |nerve P| // SSet.toTop.map (nerveMap f.monotone.functor) x = y} → E :=
    fun x => ⟨orderComplexCoordinates P x.val,
      orderComplexCoordinates_positiveSupport_card_le P N hP x.val,
      (orderComplexCoordinates_natural f x.val).symm.trans
        (congrArg (orderComplexCoordinates Q) x.property)⟩
  apply Finite.of_injective e
  intro x z hxz
  apply Subtype.ext
  apply orderComplexCoordinates_injective P
  exact congrArg Subtype.val hxz

end KIP126.Topology.SimplicialRealization
