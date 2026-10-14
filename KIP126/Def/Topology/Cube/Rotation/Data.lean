module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.UnitInterval

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- The nonsingular linear interpolation to clockwise quarter rotation. -/
noncomputable def quarterLinear (s : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - s) * v.1 + s * v.2, (1 - s) * v.2 - s * v.1)

/-- Radial normalization in the maximum norm preserves each concentric square. -/
noncomputable def quarterRadial (s : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (‖v‖ / ‖quarterLinear s v‖) • quarterLinear s v

/-- Coordinates centered at the midpoint of the unit square. -/
noncomputable def squareCenter (p : I × I) : ℝ × ℝ :=
  (2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1)

/-- A quarter-rotation path of the square; clipping only packages its range. -/
noncomputable def squareRotation (s : I) (p : I × I) : I × I :=
  (Set.projIcc 0 1 zero_le_one ((quarterRadial s (squareCenter p)).1 / 2 + 1 / 2),
   Set.projIcc 0 1 zero_le_one ((quarterRadial s (squareCenter p)).2 / 2 + 1 / 2))

end KIP126.Topology.Cube
