import KIP126.Mathlib.ClassicalAdams.StandardPage.Data
import KIP126.Main.Solution.Computation.Dimension
import KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs

namespace KIP126.Classical.Adams

open CategoryTheory

/-- Both constructions pick the unique nonzero element in bidegree `(2,128)`.
The comparison follows from the proved degree bound and standard nonvanishing;
it is not an additional axiom or a consequence of matching generator names. -/
theorem h6Square_comparison :
    toStandardE2 (2, 128) computedH6Square = sphereH6Square := by
  let e := sphereAdams_towerComparison.pageIso 2 (by decide) (2, 128)
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective e.hom).1 inferInstance sphereH6Square
  have hn : x ≠ 0 := by
    intro h
    apply sphereH6Square_ne_zero
    exact hx.symm.trans ((congrArg e.hom.hom h).trans (map_zero _))
  have he := sphereAdamsData_eq_computedH6Square_of_ne_zero x hn
  subst x
  exact hx

end KIP126.Classical.Adams
