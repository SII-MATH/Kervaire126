module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- Coordinatewise affine expansion of a chosen subcube, clipped at the
original cube boundary. -/
noncomputable def windowCompression {N : Type*} (a b : N → I) : C((N → I), (N → I)) :=
  ⟨fun x i => Set.projIcc 0 1 zero_le_one (((x i : ℝ) - a i) / ((b i : ℝ) - a i)),
    continuous_pi fun i => continuous_projIcc.comp
      (((continuous_apply i).subtype_val.sub continuous_const).div_const _)⟩

/-- Straight interpolation to window compression, packaged inside the
actual unit cube. Each original boundary face stays a boundary face. -/
noncomputable def windowCompressionInterpolation {N : Type*} (a b : N → I) :
    C(I × (N → I), (N → I)) :=
  ⟨fun z i => Set.projIcc 0 1 zero_le_one
      ((1 - (z.1 : ℝ)) * z.2 i + (z.1 : ℝ) * windowCompression a b z.2 i),
    continuous_pi fun i => continuous_projIcc.comp (by
      exact (continuous_const.sub continuous_fst.subtype_val).mul
        (((continuous_apply i).comp continuous_snd).subtype_val) |>.add
          (continuous_fst.subtype_val.mul
            (((continuous_apply i).comp ((windowCompression a b).continuous.comp continuous_snd)).subtype_val)))⟩

end KIP126.Topology.Cube
