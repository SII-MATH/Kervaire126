module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Window.Proofs
public import KIP126.Def.Topology.Cube.Compression.Neighborhood.Proofs
public import KIP126.Def.Topology.Collapse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Set KIP126.Topology KIP126.Topology.Cube
open scoped unitInterval OnePoint
set_option backward.isDefEq.respectTransparency false

/-- Every actual neighborhood of a nonbasepoint contains a spherical
coordinate window containing that point. -/
theorem exists_sphereWindow_within (n : ℕ) (y : sphereLevel n)
    (hy : y ≠ (sphereLevel n).point) (U : Set (sphereLevel n))
    (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ a b : Fin n → I, (∀ i, a i < b i) ∧
      y ∈ sphereWindow n a b ∧ sphereWindow n a b ⊆ U := by
  obtain ht | ⟨t, ht⟩ := sphereLevel_eq_point_or_sphereCube n y
  · exact False.elim (hy ht)
  have htb : t ∉ _root_.Cube.boundary (Fin n) := by
    intro h
    exact hy (ht.trans ((sphereCube_eq_point_iff_boundary n t).mpr h))
  obtain ⟨a, b, hab, hw⟩ := exists_window_within t htb
    ((sphereCube n) ⁻¹' U) (hU.preimage (sphereCube n).val.continuous)
      (by change sphereCube n t ∈ U; exact ht ▸ hyU)
  refine ⟨a, b, fun i => (hab i).2.1.trans (hab i).2.2.1,
    ⟨t, fun i => ⟨(hab i).2.1, (hab i).2.2.1⟩, ht.symm⟩, ?_⟩
  rintro x ⟨u, hu, rfl⟩
  exact hw hu

/-- The one-point compactification of the actual window is identified
with the original sphere by the original compression, with infinity
going to the original basepoint. Thus the single local branch is an
actual homeomorphism, not merely a continuous collapse factor. -/
theorem exists_onePoint_sphereWindow_homeomorph (n : ℕ) (a b : Fin n → I)
    (hab : ∀ i, a i < b i) :
    ∃ e : OnePoint (sphereWindow n a b) ≃ₜ sphereLevel n,
      e ∞ = (sphereLevel n).point ∧
      ∀ z : sphereWindow n a b,
        e (z : OnePoint (sphereWindow n a b)) =
          (sphereWindowCompression n a b hab).map z.val := by
  letI := sphereLevel_compactSpace n
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  let V := sphereWindow n a b
  have hV := sphereWindow_isOpen n a b hab
  obtain ⟨c₀, hc₀, hc⟩ := exists_collapse_homeomorph_onePoint Vᶜ
    hV.isClosed_compl ⟨(sphereLevel n).point, sphereLevel_point_not_mem_window n a b⟩
  let c := c₀.trans (Homeomorph.setCongr (compl_compl V)).onePointCongr
  have hcp : c (Quot.mk _ (sphereLevel n).point) = ∞ := by
    change (Homeomorph.setCongr (compl_compl V)).onePointCongr (c₀ _) = ∞
    rw [hc₀]
    rfl
  have hcv (z : V) : c (Quot.mk _ z.val) = (z : OnePoint V) := by
    change (Homeomorph.setCongr (compl_compl V)).onePointCongr (c₀ _) = _
    rw [hc ⟨z.val, by simpa using z.property⟩]
    rfl
  obtain ⟨d, hd⟩ := exists_sphereWindow_collapse_homeomorph n a b hab
  refine ⟨c.symm.trans d, ?_, ?_⟩
  · change d (c.symm ∞) = _
    rw [← hcp, c.symm_apply_apply]
    exact (hd _).trans (sphereWindowCompression n a b hab).point
  · intro z
    change d (c.symm (z : OnePoint V)) = _
    rw [← hcv z, c.symm_apply_apply]
    exact hd _

end KIP126.StableHomotopy.Implementation.Prespectrum
