module

public import KIP126.Def.Topology.Coproduct.Wedge.Proofs
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

namespace KIP126.Topology

open scoped OnePoint

universe u v
variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)]
  [∀ j, T2Space (X j)]

/-- The actual proper summand inclusions extend over infinity and agree at
the common point of the quotient wedge. -/
def onePointWedgeToSigma :
    C(Wedge (fun j => OnePoint (X j)) (fun _ => ∞), OnePoint (Σ j, X j)) :=
  wedgeDesc _ _ ∞ (fun j => ⟨OnePoint.map (Sigma.mk j),
    OnePoint.continuous_map continuous_sigmaMk (by
      rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
      exact _root_.Topology.IsClosedEmbedding.sigmaMk.tendsto_cocompact)⟩)
    (fun _ => rfl)

end KIP126.Topology
