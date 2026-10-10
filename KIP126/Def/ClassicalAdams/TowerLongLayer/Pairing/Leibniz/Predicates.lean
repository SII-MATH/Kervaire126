import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Page.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Boundary.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)

/-- The two-term boundary identity on long-layer representatives, already
projected to the target quotient. `L` and `R` must be the intended pairings
in the two differential bidegrees, with their target casts supplied explicitly.
The integer `e` records the chosen sign. No value or witness is postulated. -/
def AdamsLongLayerPairing.RelativeBoundaryFormula
    (L : adamsPage unit X r hr (p.1 + r) (p.2 + r - 1) →ₗ[ℤ]
      adamsPage unit X r hr q.1 q.2 →ₗ[ℤ]
        adamsPage unit X r hr ((p.1 + q.1) + r) ((p.2 + q.2) + r - 1))
    (R : adamsPage unit X r hr p.1 p.2 →ₗ[ℤ]
      adamsPage unit X r hr (q.1 + r) (q.2 + r - 1) →ₗ[ℤ]
        adamsPage unit X r hr ((p.1 + q.1) + r) ((p.2 + q.2) + r - 1))
    (e : ℤ) : Prop :=
  ∀ a b, adamsLongLayerBoundaryToPage unit X r hr (p.1 + q.1) (p.2 + q.2) (P.long a b) =
    L (adamsLongLayerBoundaryToPage unit X r hr p.1 p.2 a)
        (adamsLongLayerToPage unit X r hr q.1 q.2 b) +
      e • R (adamsLongLayerToPage unit X r hr p.1 p.2 a)
        (adamsLongLayerBoundaryToPage unit X r hr q.1 q.2 b)

end
end KIP126.Classical.Adams
