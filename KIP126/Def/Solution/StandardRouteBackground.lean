import KIP126.Def.StageInput.StandardSphere.Background.Data
import KIP126.Def.StageInput.StandardSphere.Route.Fixed

/-! Construction of the structural mathematics of the selected synthetic
route. The ring detector is the existing route detector, and the algebras,
realization comparisons and May context use this route's existing objects
and functors. None of these constructions chooses a second implementation,
asserts a program-coordinate theorem, or supplies an external source result.
The construction and internal compatibility proofs remain unfinished. -/

namespace KIP126.Def.Solution

/-- Construct all structural comparisons for the explicitly selected route.
The `sorry` exposes this Def construction obligation; it does not stand for
a source theorem or a separate project axiom. -/
noncomputable def standardRouteBackground :
    KIP126.Kervaire.Route.Background KIP126.Classical.Adams.standardRouteModel := by
  sorry

end KIP126.Def.Solution
