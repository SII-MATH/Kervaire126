module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace KIP126.Topology

universe u v w z

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} {B : Type v} {F : Type w} {G : Type z}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace G]

/-- Pull back a continuous family of fiber homeomorphisms along an actual
continuous base map. Both directions are constructed explicitly. -/
noncomputable def fiberwiseHomeomorphPullback
    (e : (B × F) ≃ₜ (B × G)) (he : ∀ x, (e x).1 = x.1) (f : C(A,B)) :
    (A × F) ≃ₜ (A × G) where
  toFun x := (x.1,(e (f x.1,x.2)).2)
  invFun x := (x.1,(e.symm (f x.1,x.2)).2)
  left_inv x := by
    refine Prod.ext (by rfl) ?_
    have h : (f x.1,(e (f x.1,x.2)).2) = e (f x.1,x.2) := by
      apply Prod.ext
      · exact (he (f x.1,x.2)).symm
      · rfl
    change (e.symm (f x.1,(e (f x.1,x.2)).2)).2 = x.2
    rw [h,e.symm_apply_apply]
  right_inv x := by
    refine Prod.ext (by rfl) ?_
    have hfst : (e.symm (f x.1,x.2)).1 = f x.1 := by
      have h := he (e.symm (f x.1,x.2))
      rw [e.apply_symm_apply] at h
      exact h.symm
    have h : (f x.1,(e.symm (f x.1,x.2)).2) = e.symm (f x.1,x.2) := by
      exact Prod.ext hfst.symm rfl
    change (e (f x.1,(e.symm (f x.1,x.2)).2)).2 = x.2
    rw [h,e.apply_symm_apply]
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.comp (e.continuous.comp ((f.continuous.comp continuous_fst).prodMk continuous_snd)))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.comp (e.symm.continuous.comp ((f.continuous.comp continuous_fst).prodMk continuous_snd)))

end KIP126.Topology
