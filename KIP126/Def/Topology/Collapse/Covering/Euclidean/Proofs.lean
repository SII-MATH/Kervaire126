module

public import KIP126.Def.Topology.Collapse.Covering.Proofs
public import KIP126.Def.Topology.Ball.Charts.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
set_option backward.isDefEq.respectTransparency false

/-- A genuine covering and a genuine Euclidean target chart admit an
arbitrarily small Euclidean evenly covered neighborhood. The original
covering map remains the first coordinate of its trivialization. -/
theorem exists_euclidean_covering_chart_within
    {X Y I E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → Y} {y : Y} (h : IsEvenlyCovered f y I)
    (W : Set Y) (hW : IsOpen W) (e : W ≃ₜ E) (hyW : y ∈ W)
    (U : Set Y) (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ V : Set Y, y ∈ V ∧ IsOpen V ∧ V ⊆ U ∩ W ∧ Nonempty (V ≃ₜ E) ∧
      IsOpen (f ⁻¹' V) ∧ ∃ H : (f ⁻¹' V) ≃ₜ V × I,
        ∀ x, (H x).1.val = f x := by
  obtain ⟨hI, A, hyA, hA, hfA, H, hH⟩ := h
  obtain ⟨V, hyV, hV, hVA, heV⟩ :=
    exists_euclidean_neighborhood_within W hW e ⟨y, hyW⟩ (U ∩ A)
      (hU.inter hA) ⟨hyU, hyA⟩
  have hsub : V ⊆ A := fun _ hx => (hVA hx).1.2
  let H' : (f ⁻¹' V) ≃ₜ V × I := {
    toFun := fun x =>
      (⟨(H ⟨x.val, hsub x.property⟩).1.val, by rw [hH]; exact x.property⟩,
        (H ⟨x.val, hsub x.property⟩).2)
    invFun := fun z =>
      ⟨H.symm (⟨z.1.val, hsub z.1.property⟩, z.2), by
        change f (H.symm _) ∈ V
        rw [← hH, H.apply_symm_apply]
        exact z.1.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change (H.symm (H ⟨x.val, hsub x.property⟩)).val = x.val
      exact congrArg Subtype.val (H.symm_apply_apply ⟨x.val, hsub x.property⟩)
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun a : A × I => a.1.val)
          (H.apply_symm_apply (⟨z.1.val, hsub z.1.property⟩, z.2))
      · change (H (H.symm (⟨z.1.val, hsub z.1.property⟩, z.2))).2 = z.2
        exact congrArg Prod.snd (H.apply_symm_apply (⟨z.1.val, hsub z.1.property⟩, z.2))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  refine ⟨V, hyV, hV, (fun _ hx => ⟨(hVA hx).1.1, (hVA hx).2⟩), heV, ?_,
    H', fun x => hH ⟨x.val, hsub x.property⟩⟩
  have hf : ContinuousOn f (f ⁻¹' A) := by
    rw [continuousOn_iff_continuous_restrict]
    exact ((continuous_subtype_val.comp continuous_fst).comp H.continuous).congr hH
  have heq : (f ⁻¹' A) ∩ (f ⁻¹' V) = f ⁻¹' V :=
    Set.inter_eq_right.mpr (Set.preimage_mono hsub)
  rw [← heq]
  exact hf.isOpen_inter_preimage hfA hV

end KIP126.Topology
