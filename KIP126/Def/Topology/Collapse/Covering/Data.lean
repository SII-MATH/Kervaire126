module

public import KIP126.Def.Topology.Collapse.Wedge.Proofs
public import Mathlib.Topology.Covering.Basic

@[expose] public section

namespace KIP126.Topology

universe u v

/-- A disjoint union of copies of a space is its product with the discrete
set indexing the copies. The second coordinate records the actual sheet. -/
def sigmaConstHomeomorphProd (J : Type u) (Y : Type v)
    [TopologicalSpace J] [DiscreteTopology J] [TopologicalSpace Y] :
    (Σ _ : J, Y) ≃ₜ Y × J where
  toEquiv := (Equiv.sigmaEquivProd J Y).trans (Equiv.prodComm J Y)
  continuous_toFun := continuous_sigma fun _ => continuous_id.prodMk continuous_const
  continuous_invFun := continuous_prod_of_discrete_right.mpr fun j => by
    change Continuous (fun x : Y => (⟨j, x⟩ : Σ _ : J, Y))
    exact @continuous_sigmaMk J (fun _ => Y) (fun _ => inferInstance) j

end KIP126.Topology
