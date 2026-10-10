import KIP126.Def.ClassicalAdams.TowerLongLayer.Page.Proofs
import Mathlib.LinearAlgebra.Quotient.Bilinear

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Candidate pairings on actual one-step and long-layer homotopy groups.
This record does not postulate a pairing or any compatibility. A geometric
construction must supply these maps and the separate predicates below. -/
structure AdamsLongLayerPairing (r : ℕ) (hr : 1 ≤ r) (p q : ℤ × ℤ) where
  first : adamsE1 unit X p.1 p.2 →ₗ[ℤ] adamsE1 unit X q.1 q.2 →ₗ[ℤ]
    adamsE1 unit X (p.1 + q.1) (p.2 + q.2)
  long : HomotopyGroup (p.2 - p.1) (adamsLongLayer unit X r hr p.1) →ₗ[ℤ]
    HomotopyGroup (q.2 - q.1) (adamsLongLayer unit X r hr q.1) →ₗ[ℤ]
      HomotopyGroup ((p.2 + q.2) - (p.1 + q.1))
        (adamsLongLayer unit X r hr (p.1 + q.1))

end
end KIP126.Classical.Adams
