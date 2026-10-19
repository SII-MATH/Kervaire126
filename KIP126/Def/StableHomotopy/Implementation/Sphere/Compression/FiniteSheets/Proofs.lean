module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Support.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Proofs
public import KIP126.Def.Topology.Collapse.Covering.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology
open scoped OnePoint
set_option backward.isDefEq.respectTransparency false

/-- A genuine finite covering neighborhood gives a finite-sheet
factorization of an original map to the fixed sphere, after an actual
homotopy fixing the original basepoint. The factorization uses the
actual complement quotient and actual wedge, and every branch is the
same restriction of the constructed target compression. -/
theorem exists_sphere_map_finite_sheet_factorization
    (n : ℕ) (X : BasedSpace) [CompactSpace X] [T2Space X]
    {I : Type*} [TopologicalSpace I] [Finite I]
    (f : X ⟶ sphereLevel n) (y : sphereLevel n) (hy : y ≠ (sphereLevel n).point)
    (h : IsEvenlyCovered f.map y I) :
    ∃ V : Set (sphereLevel n), y ∈ V ∧ IsOpen V ∧ f.map X.point ∉ V ∧
      ∃ e : Quot (fun a b : X => f.map a ∉ V ∧ f.map b ∉ V) ≃ₜ
          Wedge (fun _ : I => OnePoint V) (fun _ => ∞),
        e (Quot.mk _ X.point) = wedgePoint _ _ ∧
        ∃ r : C(OnePoint V, sphereLevel n), ∃ hr : r ∞ = (sphereLevel n).point,
          ∃ g : X ⟶ sphereLevel n,
            Nonempty (ContinuousMap.HomotopyRel g.map f.map {X.point}) ∧
            ∀ x, g.map x =
              wedgeDesc _ _ (sphereLevel n).point (fun _ : I => r) (fun _ => hr)
                (e (Quot.mk _ x)) := by
  letI := sphereLevel_compactSpace n
  letI := (exists_sphereLevel_homeomorph_onePoint n).choose.isEmbedding.t2Space
  have hxy : f.map X.point ≠ y := by rw [f.point]; exact Ne.symm hy
  obtain ⟨V, hyV, hV, hxV, _, _, e, c, he₀, hc₀, _, _, hmap⟩ :=
    exists_covering_collapse_wedge_map f.map y X.point hxy h
  obtain ⟨q, ⟨Hq⟩, hq⟩ := exists_sphere_compression_supported_in n y hy V hV hyV
  have hrel : ∀ a b : sphereLevel n, (a ∉ V ∧ b ∉ V) → q.map a = q.map b :=
    fun a b hab => (hq a hab.1).trans (hq b hab.2).symm
  let raw : C(Quot (fun a b : sphereLevel n => a ∉ V ∧ b ∉ V), sphereLevel n) :=
    ⟨Quot.lift q.map hrel, continuous_quot_lift hrel q.map.continuous⟩
  let r : C(OnePoint V, sphereLevel n) := raw.comp ⟨c.symm, c.symm.continuous⟩
  have hr : r ∞ = (sphereLevel n).point := by
    change raw (c.symm ∞) = _
    calc
      raw (c.symm ∞) = raw (Quot.mk _ (f.map X.point)) :=
        congrArg raw (c.symm_apply_eq.mpr hc₀.symm)
      _ = q.map (f.map X.point) := rfl
      _ = (sphereLevel n).point := by rw [f.point, q.point]
  let fold := wedgeDesc (fun _ : I => OnePoint V) (fun _ => ∞) ∞
    (fun _ => ContinuousMap.id _) (fun _ => rfl)
  let foldr := wedgeDesc (fun _ : I => OnePoint V) (fun _ => ∞)
    (sphereLevel n).point (fun _ => r) (fun _ => hr)
  have hfold (w : Wedge (fun _ : I => OnePoint V) (fun _ => ∞)) :
      r (fold w) = foldr w := by
    induction w using Quotient.inductionOn with
    | h w =>
      cases w with
      | inl z => rcases z with ⟨i, z⟩; rfl
      | inr z => exact hr
  refine ⟨V, hyV, hV, hxV, e, he₀, r, hr, f ≫ q, ⟨{
    toFun := fun z => Hq (z.1, f.map z.2)
    continuous_toFun := Hq.continuous.comp (continuous_fst.prodMk
      (f.map.continuous.comp continuous_snd))
    map_zero_left := fun x => Hq.apply_zero _
    map_one_left := fun x => Hq.apply_one _
    prop' := ?_ }⟩, ?_⟩
  · intro s x hx
    have hx' : x = X.point := Set.mem_singleton_iff.mp hx
    subst x
    change Hq (s, f.map X.point) = q.map (f.map X.point)
    rw [f.point]
    exact Hq.eq_fst s (Set.mem_singleton _)
  · intro x
    calc
      (f ≫ q).map x = q.map (f.map x) := rfl
      _ = r (c (collapsePreimageMap f.map Vᶜ (Quot.mk _ x))) := by
        change q.map (f.map x) = raw (c.symm (c (Quot.mk _ (f.map x))))
        rw [c.symm_apply_apply]
        rfl
      _ = r (fold (e (Quot.mk _ x))) := congrArg r (hmap (Quot.mk _ x))
      _ = foldr (e (Quot.mk _ x)) := hfold _

end KIP126.StableHomotopy.Implementation.Prespectrum
