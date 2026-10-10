import KIP126.Mathlib.ClassicalAdams.StandardSphere.Data
import KIP126.Def.StageInput.StandardSphere.Sequence.Data
import KIP126.Def.SpectralSequence.Permanence.Predicates
import KIP126.Mathlib.SpectralSequence.Permanence.Data

namespace KIP126.Classical.Adams

open CategoryTheory KIP126.Core.SpectralSequence

/-- Comparison with the constructed tower on every finite page, respecting
both differentials and passage to the successor page. An E₂-only isomorphism
would not identify spectral sequences and is deliberately insufficient. -/
structure SphereTowerComparison where
  pageIso : ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ),
    sphereAdamsData.Page r p ≅ (sphereAdams.page r hr).X p
  differential : ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ),
    sphereAdamsData.d r p ≫ (pageIso r hr (p + sphereAdamsData.diffDeg r)).hom =
      (pageIso r hr p).hom ≫
        (sphereAdams.page r hr).d p (p + sphereAdamsData.diffDeg r)
  passage : ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (x : sphereAdamsData.Page r p) (y : sphereAdamsData.Page (r + 1) p)
    (hx : ((sphereAdams.page r hr).d p ((classicalAdamsShape r).next p))
      ((pageIso r hr p).hom x) = 0),
    NextPageRelation sphereAdamsData r p x y ↔
      nextPageClass sphereAdams r hr p ((pageIso r hr p).hom x) hx =
        (pageIso (r + 1) (by omega) p).hom y

end KIP126.Classical.Adams
