module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Representatives.Fibers.Proofs
public import KIP126.Def.Topology.Cube.Compression.Neighborhood.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology.Cube
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Every neighborhood of a nonbasepoint contains the entire support of
an actual compression of the fixed sphere, homotopic to its identity
relative to the original basepoint. -/
theorem exists_sphere_compression_supported_in (n : ℕ)
    (y : sphereLevel n) (hy : y ≠ (sphereLevel n).point)
    (U : Set (sphereLevel n)) (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ q : sphereLevel n ⟶ sphereLevel n,
      Nonempty (ContinuousMap.HomotopyRel q.map (ContinuousMap.id (sphereLevel n))
        {(sphereLevel n).point}) ∧
      ∀ z, z ∉ U → q.map z = (sphereLevel n).point := by
  obtain ht | ⟨t, ht⟩ := sphereLevel_eq_point_or_sphereCube n y
  · exact False.elim (hy ht)
  have htb : t ∉ _root_.Cube.boundary (Fin n) := by
    intro h
    exact hy (ht.trans ((sphereCube_eq_point_iff_boundary n t).mpr h))
  obtain ⟨a, b, hab, hwindow⟩ := exists_window_within t htb
    ((sphereCube n) ⁻¹' U) (hU.preimage (sphereCube n).val.continuous)
      (by change sphereCube n t ∈ U; exact ht ▸ hyU)
  have hab' (i : Fin n) : a i < b i := (hab i).2.1.trans (hab i).2.2.1
  refine ⟨sphereWindowCompression n a b hab', sphereWindowCompression_homotopic_id n a b hab', ?_⟩
  intro z hz
  rcases sphereLevel_eq_point_or_sphereCube n z with rfl | ⟨u, rfl⟩
  · exact (sphereWindowCompression n a b hab').point
  · exact sphereWindowCompression_eq_point_outside n a b hab' u (fun hu => hz (hwindow hu))

/-- Postcomposing an original based map with the constructed sphere
compression preserves its actual based homotopy class and makes it
strictly constant outside the inverse image of the chosen neighborhood. -/
theorem exists_sphere_map_supported_in_preimage (n : ℕ) (X : BasedSpace)
    (f : X ⟶ sphereLevel n) (y : sphereLevel n) (hy : y ≠ (sphereLevel n).point)
    (U : Set (sphereLevel n)) (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ g : X ⟶ sphereLevel n,
      Nonempty (ContinuousMap.HomotopyRel g.map f.map {X.point}) ∧
      ∀ x, f.map x ∉ U → g.map x = (sphereLevel n).point := by
  obtain ⟨q, ⟨H⟩, hq⟩ := exists_sphere_compression_supported_in n y hy U hU hyU
  refine ⟨f ≫ q, ⟨{
    toFun := fun z => H (z.1, f.map z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      (f.map.continuous.comp continuous_snd))
    map_zero_left := fun x => H.apply_zero _
    map_one_left := fun x => H.apply_one _
    prop' := ?_ }⟩, fun x hx => hq (f.map x) hx⟩
  intro s x hx
  have hx' : x = X.point := Set.mem_singleton_iff.mp hx
  subst x
  change H (s, f.map X.point) = q.map (f.map X.point)
  rw [f.point]
  exact H.eq_fst s (Set.mem_singleton _)

end KIP126.StableHomotopy.Implementation.Prespectrum
