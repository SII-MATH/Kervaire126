module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval

/-- The affine interval parameter which inserts the reverse outer cone
path continuously in front of the original inner cone path. -/
noncomputable def coneIterationParameter (s t : I) : I :=
  ⟨(1 - (t : ℝ) + (1 + (t : ℝ)) * (s : ℝ)) / 2, by
    constructor
    · nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, mul_nonneg s.2.1 t.2.1]
    · nlinarith [s.2.1, s.2.2, t.2.1, t.2.2,
        mul_nonneg (sub_nonneg.mpr s.2.2) (add_nonneg (by norm_num : (0:ℝ) ≤ 1) t.2.1)]⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
