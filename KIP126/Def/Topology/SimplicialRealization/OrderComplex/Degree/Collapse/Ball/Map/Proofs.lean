module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Degree.Collapse.Ball.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite Simplex Set
open scoped Classical OnePoint
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original realized order map admits a finite sphere-piece collapse:
the neighborhood is genuinely Euclidean, each one-point compactification
is a sphere, and the original induced quotient map is the actual wedge
fold. All pieces are indexed by the original fiber over the chosen point. -/
theorem exists_orderMap_full_support_ball_collapse
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (f : P →o Q) (n : ℕ)
    (hP : OrderChainSizeLE P (n + 1)) (hQ : OrderChainSizeLE Q (n + 1))
    (y : |nerve Q|)
    (hy : (positiveSupport (orderComplexCoordinates Q y)).card = n + 1)
    (x₀ : |nerve P|)
    (hxy : SSet.toTop.map (nerveMap f.monotone.functor) x₀ ≠ y) :
    ∃ V : Set |nerve Q|, y ∈ V ∧ IsOpen V ∧
      SSet.toTop.map (nerveMap f.monotone.functor) x₀ ∉ V ∧
      Nonempty (V ≃ₜ (Fin n → ℝ)) ∧
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
  let F := (SSet.toTop.map (nerveMap f.monotone.functor)).hom
  let J := {x : |nerve P| // F x = y}
  letI := finite_nerve_of_finite_order P
  letI := finite_nerve_of_finite_order Q
  letI := compactSpace_of_finite (nerve P)
  letI := compactSpace_of_finite (nerve Q)
  letI := (exists_orderComplexCoordinates_homeomorph P).choose.isEmbedding.t2Space
  letI := (exists_orderComplexCoordinates_homeomorph Q).choose.isEmbedding.t2Space
  obtain ⟨hfinite, V, hyV, hV, hxV, heV, H, hH⟩ :=
    exists_orderMap_full_support_ball_chart f n hP hQ y hy x₀ hxy
  letI : Finite J := hfinite
  have hcover := orderMap_isCoveringMapOn_full_support f (n + 1) hP hQ y hy
  change IsEvenlyCovered F y J at hcover
  letI := hcover.1
  let S : Set |nerve P| := (F ⁻¹' V)ᶜ
  have hS : IsClosed S := (hV.preimage F.continuous).isClosed_compl
  letI := hV.locallyCompactSpace
  obtain ⟨cX, hcX₀, hcX⟩ := exists_collapse_homeomorph_onePoint S hS ⟨x₀, hxV⟩
  let a : (Sᶜ : Set |nerve P|) ≃ₜ (Σ _ : J, V) :=
    ((Homeomorph.setCongr (compl_compl (F ⁻¹' V))).trans H).trans
      (sigmaConstHomeomorphProd J V).symm
  obtain ⟨b, hb₀, hb⟩ := exists_onePointWedge_homeomorph_sigma (fun _ : J => V)
  let e := (cX.trans a.onePointCongr).trans b.symm
  have he₀ : e (Quot.mk _ x₀) = wedgePoint _ _ := by
    change b.symm (a.onePointCongr (cX (Quot.mk _ x₀))) = _
    rw [hcX₀]
    exact b.symm_apply_eq.mpr hb₀.symm
  have he (x : F ⁻¹' V) : e (Quot.mk _ x.val) =
      wedgeInclusion _ _ (H x).2 ((H x).1 : OnePoint V) := by
    change b.symm (a.onePointCongr (cX (Quot.mk _ x.val))) = _
    rw [hcX ⟨x.val, by simpa [S] using x.property⟩]
    exact b.symm_apply_eq.mpr (hb (H x).2 ((H x).1 : OnePoint V)).symm
  obtain ⟨cY, hcY₀, hcY⟩ :=
    exists_collapse_homeomorph_onePoint Vᶜ hV.isClosed_compl ⟨F x₀, hxV⟩
  let c := cY.trans (Homeomorph.setCongr (compl_compl V)).onePointCongr
  have hc₀ : c (Quot.mk _ (F x₀)) = ∞ := by
    change (Homeomorph.setCongr (compl_compl V)).onePointCongr (cY _) = ∞
    rw [hcY₀]
    rfl
  have hc (z : V) : c (Quot.mk _ z.val) = (z : OnePoint V) := by
    change (Homeomorph.setCongr (compl_compl V)).onePointCongr (cY _) = _
    rw [hcY ⟨z.val, by simpa using z.property⟩]
    rfl
  refine ⟨V, hyV, hV, hxV, heV, e, c, he₀, hc₀, ?_⟩
  intro q
  induction q using Quot.inductionOn with
  | h x =>
    rw [collapsePreimageMap_mk]
    let fold := wedgeDesc (fun _ : J => OnePoint V) (fun _ => ∞) ∞
      (fun _ => ContinuousMap.id _) (fun _ => rfl)
    by_cases hx : F x ∈ V
    · calc
        c (Quot.mk _ (F x)) = ((⟨F x, hx⟩ : V) : OnePoint V) := hc ⟨F x, hx⟩
        _ = ((H ⟨x, hx⟩).1 : OnePoint V) :=
          congrArg (fun z : V => (z : OnePoint V)) (Subtype.ext (hH ⟨x, hx⟩).symm)
        _ = fold (wedgeInclusion _ _ (H ⟨x, hx⟩).2 ((H ⟨x, hx⟩).1 : OnePoint V)) := rfl
        _ = fold (e (Quot.mk _ x)) := congrArg fold (he ⟨x, hx⟩).symm
    · have hEx : (Quot.mk (fun a b : |nerve P| => F a ∉ V ∧ F b ∉ V) x) =
          Quot.mk _ x₀ := Quot.sound ⟨hx, hxV⟩
      have hYx : (Quot.mk (fun a b : |nerve Q| => a ∉ V ∧ b ∉ V) (F x)) =
          Quot.mk _ (F x₀) := Quot.sound ⟨hx, hxV⟩
      calc
        c (Quot.mk _ (F x)) = c (Quot.mk _ (F x₀)) := congrArg c hYx
        _ = ∞ := hc₀
        _ = fold (wedgePoint _ _) := rfl
        _ = fold (e (Quot.mk _ x₀)) := congrArg fold he₀.symm
        _ = fold (e (Quot.mk _ x)) := congrArg (fun q => fold (e q)) hEx.symm

end KIP126.Topology.SimplicialRealization
