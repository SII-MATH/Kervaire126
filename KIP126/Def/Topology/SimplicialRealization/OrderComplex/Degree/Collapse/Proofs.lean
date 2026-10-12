module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.Covering.Proofs
public import KIP126.Def.Topology.Collapse.Covering.Map.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex
open scoped Classical OnePoint
universe u
set_option backward.isDefEq.respectTransparency false

/-- For the original realized order map, a full-dimensional target point
has a finite-sheet neighborhood whose complement-collapse is the actual
wedge indexed by that point's actual fiber. Under the two displayed
homeomorphisms, the original quotient map is exactly the fold map. -/
theorem exists_orderMap_full_support_collapse_wedge
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (N : ℕ) (hP : OrderChainSizeLE P N) (hQ : OrderChainSizeLE Q N)
    (y : |nerve Q|) (hy : (positiveSupport (orderComplexCoordinates Q y)).card = N)
    (x₀ : |nerve P|)
    (hxy : SSet.toTop.map (nerveMap f.monotone.functor) x₀ ≠ y) :
    ∃ V : Set |nerve Q|, y ∈ V ∧ IsOpen V ∧
      SSet.toTop.map (nerveMap f.monotone.functor) x₀ ∉ V ∧
      ∃ e : Quot (fun a b : |nerve P| =>
          SSet.toTop.map (nerveMap f.monotone.functor) a ∉ V ∧
          SSet.toTop.map (nerveMap f.monotone.functor) b ∉ V) ≃ₜ
        Wedge (fun _ : {x : |nerve P| //
          SSet.toTop.map (nerveMap f.monotone.functor) x = y} => OnePoint V) (fun _ => ∞),
      ∃ c : Quot (fun a b : |nerve Q| => a ∉ V ∧ b ∉ V) ≃ₜ OnePoint V,
        e (Quot.mk _ x₀) = wedgePoint _ _ ∧
        c (Quot.mk _ (SSet.toTop.map (nerveMap f.monotone.functor) x₀)) = ∞ ∧
        ∀ q, c (collapsePreimageMap
            (SSet.toTop.map (nerveMap f.monotone.functor)).hom Vᶜ q) =
          wedgeDesc _ _ ∞ (fun _ => ContinuousMap.id _) (fun _ => rfl) (e q) := by
  letI := finite_nerve_of_finite_order P
  letI := finite_nerve_of_finite_order Q
  letI := compactSpace_of_finite (nerve P)
  letI := compactSpace_of_finite (nerve Q)
  letI := (exists_orderComplexCoordinates_homeomorph P).choose.isEmbedding.t2Space
  letI := (exists_orderComplexCoordinates_homeomorph Q).choose.isEmbedding.t2Space
  letI := finite_orderMap_fiber_of_full_support f N hP y hy
  have hcover := orderMap_isCoveringMapOn_full_support f N hP hQ y hy
  change IsEvenlyCovered (SSet.toTop.map (nerveMap f.monotone.functor)).hom y
    {x : |nerve P| // SSet.toTop.map (nerveMap f.monotone.functor) x = y} at hcover
  obtain ⟨V, hyV, hV, hxV, H, hH, e, c, he₀, hc₀, he, hc, hmap⟩ :=
    exists_covering_collapse_wedge_map
      (SSet.toTop.map (nerveMap f.monotone.functor)).hom y x₀ hxy hcover
  exact ⟨V, hyV, hV, hxV, e, c, he₀, hc₀, hmap⟩

end KIP126.Topology.SimplicialRealization
