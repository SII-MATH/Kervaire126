module

public import KIP126.Def.Topology.Collapse.Covering.Data
public import KIP126.Def.Topology.Collapse.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
open scoped OnePoint
set_option backward.isDefEq.respectTransparency false

/-- Restrict an actual covering chart to a smaller open neighborhood,
retaining both its base coordinate and its original sheet index. -/
theorem exists_covering_chart_within
    {E Y I : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace I]
    {f : E → Y} {y : Y} (h : IsEvenlyCovered f y I)
    {W : Set Y} (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ V : Set Y, y ∈ V ∧ IsOpen V ∧ V ⊆ W ∧ IsOpen (f ⁻¹' V) ∧
      ∃ H : (f ⁻¹' V) ≃ₜ V × I, ∀ x, (H x).1.val = f x := by
  obtain ⟨hI, U, hyU, hU, hfU, H, hH⟩ := h
  let V := U ∩ W
  let H' : (f ⁻¹' V) ≃ₜ V × I := {
    toFun := fun x =>
      (⟨(H ⟨x.val, x.property.1⟩).1.val,
        by rw [hH]; exact x.property⟩, (H ⟨x.val, x.property.1⟩).2)
    invFun := fun z =>
      ⟨H.symm (⟨z.1.val, z.1.property.1⟩, z.2), by
        change f (H.symm _) ∈ V
        rw [← hH, H.apply_symm_apply]
        exact z.1.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change (H.symm (H ⟨x.val, x.property.1⟩)).val = x.val
      exact congrArg Subtype.val (H.symm_apply_apply ⟨x.val, x.property.1⟩)
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun a : U × I => a.1.val)
          (H.apply_symm_apply (⟨z.1.val, z.1.property.1⟩, z.2))
      · change (H (H.symm (⟨z.1.val, z.1.property.1⟩, z.2))).2 = z.2
        exact congrArg Prod.snd (H.apply_symm_apply (⟨z.1.val, z.1.property.1⟩, z.2))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  refine ⟨V, ⟨hyU, hyW⟩, hU.inter hW, inter_subset_right,
    ?_, H', fun x => hH ⟨x.val, x.property.1⟩⟩
  have hf : ContinuousOn f (f ⁻¹' U) := by
    rw [continuousOn_iff_continuous_restrict]
    exact ((continuous_subtype_val.comp continuous_fst).comp H.continuous).congr hH
  -- Continuity on the original open chart suffices for the restricted preimage.
  exact hf.isOpen_inter_preimage hfU hW

/-- A finite covering near a point, separated from a selected basepoint,
gives an actual wedge decomposition after collapsing the complement of
that neighborhood's inverse image. The displayed formula tracks every
point on every original sheet. -/
theorem exists_covering_collapse_wedge
    {E Y I : Type*} [TopologicalSpace E] [CompactSpace E] [T2Space E]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TopologicalSpace I] [Finite I]
    (f : C(E, Y)) (y : Y) (x₀ : E) (hxy : f x₀ ≠ y)
    (h : IsEvenlyCovered f y I) :
    ∃ V : Set Y, y ∈ V ∧ IsOpen V ∧ f x₀ ∉ V ∧
      ∃ H : (f ⁻¹' V) ≃ₜ V × I,
        (∀ x, (H x).1.val = f x) ∧
        ∃ e : Quot (fun a b : E => f a ∉ V ∧ f b ∉ V) ≃ₜ
            Wedge (fun _ : I => OnePoint V) (fun _ => ∞),
          e (Quot.mk _ x₀) = wedgePoint _ _ ∧
          ∀ x : f ⁻¹' V, e (Quot.mk _ x.val) =
            wedgeInclusion _ _ (H x).2 ((H x).1 : OnePoint V) := by
  classical
  letI := h.1
  obtain ⟨V, hyV, hV, hVW, hfV, H, hH⟩ :=
    exists_covering_chart_within h (isClosed_singleton.isOpen_compl)
      (show y ∈ ({f x₀} : Set Y)ᶜ from Ne.symm hxy)
  have hxV : f x₀ ∉ V := fun hx => hVW hx rfl
  let S : Set E := (f ⁻¹' V)ᶜ
  have hS : IsClosed S := hfV.isClosed_compl
  letI := hV.locallyCompactSpace
  obtain ⟨c, hc₀, hc⟩ := exists_collapse_homeomorph_onePoint S hS ⟨x₀, hxV⟩
  let a : (Sᶜ : Set E) ≃ₜ (Σ _ : I, V) :=
    ((Homeomorph.setCongr (compl_compl (f ⁻¹' V))).trans H).trans
      (sigmaConstHomeomorphProd I V).symm
  obtain ⟨b, hb₀, hb⟩ := exists_onePointWedge_homeomorph_sigma (fun _ : I => V)
  let e := (c.trans a.onePointCongr).trans b.symm
  refine ⟨V, hyV, hV, hxV, H, hH, e, ?_, ?_⟩
  · change b.symm (a.onePointCongr (c (Quot.mk _ x₀))) = _
    rw [hc₀]
    exact b.symm_apply_eq.mpr hb₀.symm
  · intro x
    change b.symm (a.onePointCongr (c (Quot.mk _ x.val))) = _
    rw [hc ⟨x.val, by simpa [S] using x.property⟩]
    apply b.symm_apply_eq.mpr
    exact (hb (H x).2 ((H x).1 : OnePoint V)).symm

end KIP126.Topology
