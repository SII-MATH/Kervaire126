module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Proofs
public import KIP126.Def.Topology.Sphere.Homeomorph.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Simplex.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Stars.Data
public import KIP126.Def.Topology.Simplex.ClosedBall.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization
open KIP126.Topology Metric
set_option backward.isDefEq.respectTransparency false

/-- The original fixed sphere admits an actual finite-order boundary
model, with its original basepoint sent to any specified actual vertex.
No homotopy-group calculation or degree theorem enters this comparison. -/
theorem exists_sphereLevel_orderBoundary_homeomorph (n : ℕ)
    (p : orderProperChains (Fin (n + 2))) :
    ∃ e : sphereLevel n ≃ₜ |nerve (orderProperChains (Fin (n + 2)))|,
      e (sphereLevel n).point = orderVertex _ p := by
  obtain ⟨b, _⟩ := exists_orderBoundary_stdSimplex_homeomorph (Fin (n + 2))
  obtain ⟨s, hs⟩ := Simplex.exists_stdSimplex_closedBall_homeomorph (n + 1)
  let flatten : {z : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 // ‖z.val‖ = 1} ≃ₜ
      Metric.sphere (0 : Fin (n + 1) → ℝ) 1 := {
    toFun := fun z => ⟨z.val.val, by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property⟩
    invFun := fun z => ⟨⟨z.val, Metric.sphere_subset_closedBall z.property⟩, by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  obtain ⟨l⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Fin (n + 1) → ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) by simp)
  obtain ⟨k, _⟩ := Sphere.exists_unitSphere_homeomorph_of_continuousLinearEquiv l
  let o := b.trans ((s.subtype hs).trans (flatten.trans k))
  obtain ⟨a⟩ := exists_sphereLevel_homeomorph_euclideanSphere n
  obtain ⟨r, hr⟩ := Sphere.exists_unitSphere_homeomorph_apply_eq
    (a (sphereLevel n).point) (o (orderVertex _ p))
  refine ⟨a.trans (r.trans o.symm), ?_⟩
  change o.symm (r (a (sphereLevel n).point)) = _
  rw [hr, o.symm_apply_apply]

end KIP126.StableHomotopy.Implementation.Prespectrum
