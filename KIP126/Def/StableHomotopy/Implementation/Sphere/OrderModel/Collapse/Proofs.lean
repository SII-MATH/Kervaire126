module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OrderModel.Covering.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.FiniteSheets.Homeomorph.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology
open scoped unitInterval OnePoint
set_option backward.isDefEq.respectTransparency false

/-- Every positive-dimensional original sphere self-map admits an
actual finite-sheet collapse decomposition after based homotopy. The
quotient is taken on the same original sphere, its wedge is finite, and
each branch is an actual pointed homeomorphism to that original sphere.
No regular-value, covering, or degree hypothesis is supplied. -/
theorem exists_sphere_map_finite_collapse_decomposition (n : ℕ) (hn : 0 < n)
    (f : sphereLevel n ⟶ sphereLevel n) :
    ∃ (m : ℕ) (u g : sphereLevel n ⟶ sphereLevel n) (a b : Fin n → I),
    ∃ hab : ∀ i, a i < b i,
      Nonempty (ContinuousMap.HomotopyRel u.map f.map {(sphereLevel n).point}) ∧
      Nonempty (ContinuousMap.HomotopyRel g.map f.map {(sphereLevel n).point}) ∧
      g = u ≫ sphereWindowCompression n a b hab ∧
      ∃ e : Quot (fun x z : sphereLevel n =>
          u.map x ∉ sphereWindow n a b ∧ u.map z ∉ sphereWindow n a b) ≃ₜ
          Wedge (fun _ : Fin m => OnePoint (sphereWindow n a b)) (fun _ => ∞),
        e (Quot.mk _ (sphereLevel n).point) = wedgePoint _ _ ∧
        ∃ r : OnePoint (sphereWindow n a b) ≃ₜ sphereLevel n,
        ∃ hr : r ∞ = (sphereLevel n).point,
          ∀ x, g.map x =
            wedgeDesc (fun _ : Fin m => OnePoint (sphereWindow n a b)) (fun _ => ∞)
              (sphereLevel n).point (fun _ => ⟨r, r.continuous⟩) (fun _ => hr)
                (e (Quot.mk _ x)) := by
  classical
  letI := sphereLevel_compactSpace n
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  obtain ⟨u, hu, y, hy, hfin, hc⟩ := exists_sphere_map_homotopic_finite_covering n hn f
  let J := u.map ⁻¹' {y}
  letI : Finite J := hfin
  letI : Fintype J := Fintype.ofFinite J
  letI : DiscreteTopology J := hc.1
  let j : J ≃ₜ Fin (Fintype.card J) := (Fintype.equivFin J).toHomeomorphOfDiscrete
  obtain ⟨a, b, hab, _, e, he, r, hr, g, hgu, hg, hformula⟩ :=
    exists_sphere_map_finite_sheet_homeomorphism_factorization n (sphereLevel n)
      u y hy (hc.of_fiber_homeomorph j)
  exact ⟨Fintype.card J, u, g, a, b, hab, hu, ⟨hg.some.trans hu.some⟩,
    hgu, e, he, r, hr, hformula⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
