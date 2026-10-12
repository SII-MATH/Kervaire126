module

public import KIP126.Def.Topology.FiberBundle.Pullback.Data

@[expose] public section

namespace KIP126.Topology

variable {E A B F : Type*} [TopologicalSpace E] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace F]
set_option backward.isDefEq.respectTransparency false

/-- The actual chart product homeomorphism pulls back along any
continuous base map, with the ordinary topological fiber-product topology. -/
def pullbackChartHomeomorph (p : C(E,B)) (a : C(A,B)) (T : Bundle.Trivialization F p) :
    (pullbackSndMap p a ⁻¹' (a ⁻¹' T.baseSet)) ≃ₜ (a ⁻¹' T.baseSet) × F := by
  let V := a ⁻¹' T.baseSet
  have hsource (z : pullbackSndMap p a ⁻¹' V) : z.val.val.1 ∈ T.source := by
    apply T.mem_source.mpr
    rw [z.val.property]
    exact z.property
  have htarget (z : V × F) : (a z.1.val,z.2) ∈ T.target := T.mem_target.mpr z.1.property
  exact {
    toFun := fun z => (⟨z.val.val.2,z.property⟩,(T z.val.val.1).2)
    invFun := fun z => ⟨⟨(T.invFun (a z.1.val,z.2),z.1.val),T.proj_symm_apply (htarget z)⟩,z.1.property⟩
    left_inv := fun z => by
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ?_ rfl
      change T.invFun (a z.val.val.2,(T z.val.val.1).2) = z.val.val.1
      rw [← z.val.property]
      exact T.symm_apply_mk_proj (hsource z)
    right_inv := fun z => by
      refine Prod.ext ?_ ?_
      · rfl
      · change (T (T.invFun (a z.1.val,z.2))).2 = z.2
        exact congrArg (fun w : B × F => w.2) (T.apply_symm_apply (htarget z))
    continuous_toFun :=
      ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).prodMk
        (continuous_snd.comp (T.continuousOn_toFun.comp_continuous
          (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)) hsource))
    continuous_invFun :=
      ((T.continuousOn_invFun.comp_continuous
        ((a.continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
        htarget).prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _ |>.subtype_mk _ }

end KIP126.Topology
