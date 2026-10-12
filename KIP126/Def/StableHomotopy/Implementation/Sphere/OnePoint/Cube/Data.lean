module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Data
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open scoped unitInterval

/-- Real coordinates on the open cube, using the same odd interval
coordinate in every direction. -/
noncomputable def cubeInteriorHomeomorphReal (ι : Type*) :
    ((_root_.Cube.boundary ι)ᶜ : Set (ι → I)) ≃ₜ (ι → ℝ) where
  toFun t i := intervalInteriorHomeomorphReal ⟨t.val i,
    ⟨fun h => t.property ⟨i, Or.inl h⟩, fun h => t.property ⟨i, Or.inr h⟩⟩⟩
  invFun x := ⟨fun i => (intervalInteriorHomeomorphReal.symm (x i)).val, by
    rintro ⟨i, hi | hi⟩
    · exact (intervalInteriorHomeomorphReal.symm (x i)).property.1 hi
    · exact (intervalInteriorHomeomorphReal.symm (x i)).property.2 hi⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (intervalInteriorHomeomorphReal.symm_apply_apply _)
  right_inv x := by
    funext i
    exact intervalInteriorHomeomorphReal.apply_symm_apply (x i)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact intervalInteriorHomeomorphReal.continuous.comp
      (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_subtype_val.comp
      (intervalInteriorHomeomorphReal.symm.continuous.comp (continuous_apply i))

end KIP126.StableHomotopy.Implementation.BasedSpace
