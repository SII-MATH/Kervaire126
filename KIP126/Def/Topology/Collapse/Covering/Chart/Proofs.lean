module

public import KIP126.Def.Topology.Collapse.Covering.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
open scoped OnePoint
set_option backward.isDefEq.respectTransparency false

/-- Restrict an actual covering chart to a prescribed subset of its
base, retaining exactly that subset and the original sheet coordinate. -/
theorem exists_covering_chart_restrict
    {E Y I : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace I]
    {f : E → Y} {U V : Set Y} (hVU : V ⊆ U)
    (H : (f ⁻¹' U) ≃ₜ U × I) (hH : ∀ x, (H x).1.val = f x) :
    ∃ K : (f ⁻¹' V) ≃ₜ V × I, ∀ x, (K x).1.val = f x := by
  let K : (f ⁻¹' V) ≃ₜ V × I := {
    toFun := fun x =>
      (⟨(H ⟨x.val, hVU x.property⟩).1.val, by rw [hH]; exact x.property⟩,
        (H ⟨x.val, hVU x.property⟩).2)
    invFun := fun z =>
      ⟨H.symm (⟨z.1.val, hVU z.1.property⟩, z.2), by
        change f (H.symm _) ∈ V
        rw [← hH, H.apply_symm_apply]
        exact z.1.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change (H.symm (H ⟨x.val, hVU x.property⟩)).val = x.val
      exact congrArg Subtype.val (H.symm_apply_apply ⟨x.val, hVU x.property⟩)
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun a : U × I => a.1.val)
          (H.apply_symm_apply (⟨z.1.val, hVU z.1.property⟩, z.2))
      · change (H (H.symm (⟨z.1.val, hVU z.1.property⟩, z.2))).2 = z.2
        exact congrArg Prod.snd (H.apply_symm_apply (⟨z.1.val, hVU z.1.property⟩, z.2))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact ⟨K, fun x => hH ⟨x.val, hVU x.property⟩⟩

/-- The actual finite-sheet collapse for a prescribed open covering
chart. The neighborhood is retained exactly, allowing its target
compactification to be compared with a specified original sphere map. -/
theorem exists_chart_collapse_wedge
    {E Y I : Type*} [TopologicalSpace E] [CompactSpace E] [T2Space E]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TopologicalSpace I] [DiscreteTopology I] [Finite I]
    (f : C(E, Y)) (V : Set Y) (hV : IsOpen V)
    (x₀ : E) (hxV : f x₀ ∉ V) (H : (f ⁻¹' V) ≃ₜ V × I) :
    ∃ e : Quot (fun a b : E => f a ∉ V ∧ f b ∉ V) ≃ₜ
        Wedge (fun _ : I => OnePoint V) (fun _ => ∞),
      e (Quot.mk _ x₀) = wedgePoint _ _ ∧
      ∀ x : f ⁻¹' V, e (Quot.mk _ x.val) =
        wedgeInclusion _ _ (H x).2 ((H x).1 : OnePoint V) := by
  classical
  let S : Set E := (f ⁻¹' V)ᶜ
  have hS : IsClosed S := (hV.preimage f.continuous).isClosed_compl
  letI := hV.locallyCompactSpace
  obtain ⟨c, hc₀, hc⟩ := exists_collapse_homeomorph_onePoint S hS ⟨x₀, hxV⟩
  let a : (Sᶜ : Set E) ≃ₜ (Σ _ : I, V) :=
    ((Homeomorph.setCongr (compl_compl (f ⁻¹' V))).trans H).trans
      (sigmaConstHomeomorphProd I V).symm
  obtain ⟨b, hb₀, hb⟩ := exists_onePointWedge_homeomorph_sigma (fun _ : I => V)
  let e := (c.trans a.onePointCongr).trans b.symm
  refine ⟨e, ?_, ?_⟩
  · change b.symm (a.onePointCongr (c (Quot.mk _ x₀))) = _
    rw [hc₀]
    exact b.symm_apply_eq.mpr hb₀.symm
  · intro x
    change b.symm (a.onePointCongr (c (Quot.mk _ x.val))) = _
    rw [hc ⟨x.val, by simpa [S] using x.property⟩]
    apply b.symm_apply_eq.mpr
    exact (hb (H x).2 ((H x).1 : OnePoint V)).symm

end KIP126.Topology
