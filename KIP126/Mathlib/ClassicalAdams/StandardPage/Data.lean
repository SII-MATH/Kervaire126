import KIP126.Mathlib.ClassicalAdams.Comparison.Construction.Data

namespace KIP126.Classical.Adams

open CategoryTheory

/-- The E₂ map of the same all-page comparison used for the tower. -/
noncomputable def toStandardE2 (p : ℤ × ℤ) :
    sphereAdamsData.Page 2 p ⟶ (sphereAdams.page 2 (by decide)).X p :=
  (sphereAdams_towerComparison.pageIso 2 (by decide) p).hom

end KIP126.Classical.Adams
