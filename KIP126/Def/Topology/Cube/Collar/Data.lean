module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval

/-- Collapse a collar of each endpoint while retaining the middle half. -/
noncomputable def collarCoordinate (x : ℝ) : I := Set.projIcc 0 1 zero_le_one (2 * x - 1 / 2)

/-- The collar reparametrization, also defined on the ambient vector space. -/
noncomputable def collar (r : ℕ) (x : Fin r → ℝ) : Fin r → I := fun i => collarCoordinate (x i)

/-- Interpolate from the original cube coordinates to the collar coordinates. -/
noncomputable def collarHomotopy (r : ℕ) (s : I) (x : Fin r → I) : Fin r → I := fun i =>
  Set.projIcc 0 1 zero_le_one
    (((1 : ℝ) - (s : ℝ)) * (x i : ℝ) + (s : ℝ) * (collarCoordinate (x i) : ℝ))

end KIP126.Topology.Cube
