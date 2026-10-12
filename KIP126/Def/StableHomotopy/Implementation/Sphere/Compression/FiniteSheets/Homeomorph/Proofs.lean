module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Window.Neighborhood.Proofs
public import KIP126.Def.Topology.Collapse.Covering.Chart.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Set KIP126.Topology
open scoped OnePoint unitInterval
set_option backward.isDefEq.respectTransparency false

/-- A genuine finite covering neighborhood of a map to the original
sphere can be chosen so that every branch of its finite-sheet collapse
is the same actual pointed homeomorphism to the original sphere. The
factorized map is homotopic to the original map relative to its original
basepoint. -/
theorem exists_sphere_map_finite_sheet_homeomorphism_factorization
    (n : ℕ) (X : BasedSpace) [CompactSpace X] [T2Space X]
    {J : Type*} [TopologicalSpace J] [Finite J]
    (f : X ⟶ sphereLevel n) (y : sphereLevel n)
    (hy : y ≠ (sphereLevel n).point) (h : IsEvenlyCovered f.map y J) :
    ∃ a b : Fin n → I, ∃ hab : ∀ i, a i < b i,
      y ∈ sphereWindow n a b ∧
      ∃ e : Quot (fun x z : X =>
          f.map x ∉ sphereWindow n a b ∧ f.map z ∉ sphereWindow n a b) ≃ₜ
          Wedge (fun _ : J => OnePoint (sphereWindow n a b)) (fun _ => ∞),
        e (Quot.mk _ X.point) = wedgePoint _ _ ∧
        ∃ r : OnePoint (sphereWindow n a b) ≃ₜ sphereLevel n,
        ∃ hr : r ∞ = (sphereLevel n).point,
        ∃ g : X ⟶ sphereLevel n,
          (g = f ≫ sphereWindowCompression n a b hab) ∧
          Nonempty (ContinuousMap.HomotopyRel g.map f.map {X.point}) ∧
          ∀ x, g.map x =
            wedgeDesc (fun _ : J => OnePoint (sphereWindow n a b)) (fun _ => ∞)
              (sphereLevel n).point (fun _ => ⟨r, r.continuous⟩) (fun _ => hr)
                (e (Quot.mk _ x)) := by
  letI := sphereLevel_compactSpace n
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  obtain ⟨hJ, U, hyU, hU, _, H, hH⟩ := h
  letI := hJ
  obtain ⟨a, b, hab, hyV, hVU⟩ := exists_sphereWindow_within n y hy U hU hyU
  let V := sphereWindow n a b
  have hV : IsOpen V := sphereWindow_isOpen n a b hab
  have hxV : f.map X.point ∉ V := by
    rw [f.point]
    exact sphereLevel_point_not_mem_window n a b
  obtain ⟨K, hK⟩ := exists_covering_chart_restrict hVU H hH
  obtain ⟨e, he₀, he⟩ := exists_chart_collapse_wedge f.map V hV X.point hxV K
  obtain ⟨r, hr, hrv⟩ := exists_onePoint_sphereWindow_homeomorph n a b hab
  let q := sphereWindowCompression n a b hab
  obtain ⟨Hq⟩ := sphereWindowCompression_homotopic_id n a b hab
  let g : X ⟶ sphereLevel n := f ≫ q
  have hg : Nonempty (ContinuousMap.HomotopyRel g.map f.map {X.point}) := by
    refine ⟨{
      toFun := fun z => Hq (z.1, f.map z.2)
      continuous_toFun := Hq.continuous.comp (continuous_fst.prodMk
        (f.map.continuous.comp continuous_snd))
      map_zero_left := fun x => Hq.apply_zero _
      map_one_left := fun x => Hq.apply_one _
      prop' := ?_ }⟩
    intro s x hx
    have hx' : x = X.point := Set.mem_singleton_iff.mp hx
    subst x
    change Hq (s, f.map X.point) = q.map (f.map X.point)
    rw [f.point]
    exact Hq.eq_fst s (Set.mem_singleton _)
  refine ⟨a, b, hab, hyV, e, he₀, r, hr, g, rfl, hg, ?_⟩
  let fold := wedgeDesc (fun _ : J => OnePoint V) (fun _ => ∞)
    (sphereLevel n).point (fun _ => ⟨r, r.continuous⟩) (fun _ => hr)
  intro x
  by_cases hx : f.map x ∈ V
  · calc
      g.map x = q.map (f.map x) := rfl
      _ = r ((K ⟨x, hx⟩).1 : OnePoint V) :=
        ((hrv _).trans (congrArg q.map (hK ⟨x, hx⟩))).symm
      _ = fold (wedgeInclusion _ _ (K ⟨x, hx⟩).2 ((K ⟨x, hx⟩).1 : OnePoint V)) := rfl
      _ = fold (e (Quot.mk _ x)) := congrArg fold (he ⟨x, hx⟩).symm
  · have hEx : (Quot.mk (fun x z : X => f.map x ∉ V ∧ f.map z ∉ V) x) =
        Quot.mk _ X.point := Quot.sound ⟨hx, hxV⟩
    calc
      g.map x = (sphereLevel n).point :=
        (sphereWindowCompression_eq_point_iff n a b hab (f.map x)).mpr hx
      _ = fold (wedgePoint _ _) := rfl
      _ = fold (e (Quot.mk _ X.point)) := congrArg fold he₀.symm
      _ = fold (e (Quot.mk _ x)) := congrArg (fun z => fold (e z)) hEx.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
