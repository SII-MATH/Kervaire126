import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)

/-- Compatibility with the specified projections from long to one-step layers. -/
def AdamsLongLayerPairing.ProjectionCompatible : Prop :=
  ∀ a b, adamsLongLayerToE1 unit X r hr (p.1 + q.1) (p.2 + q.2) (P.long a b) =
    P.first (adamsLongLayerToE1 unit X r hr p.1 p.2 a)
      (adamsLongLayerToE1 unit X r hr q.1 q.2 b)

/-- Boundary conditions tested on tower-kernel and long-layer representatives.
These are explicit unproved geometric obligations, not global axioms and not
assumptions that a quotient product or Leibniz rule already exists. -/
structure AdamsLongLayerPairing.BoundaryCompatible : Prop where
  left : ∀ (a : HomotopyGroup (p.2 - p.1) (adamsTowerAt unit X p.1)),
    adamsI unit X (p.2 - p.1) (p.1 - r + 1) p.1 (by omega) a = 0 →
    ∀ b, P.first (adamsJ unit X p.1 p.2 a)
      (adamsLongLayerToE1 unit X r hr q.1 q.2 b) ∈
        adamsBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)
  right : ∀ a (b : HomotopyGroup (q.2 - q.1) (adamsTowerAt unit X q.1)),
    adamsI unit X (q.2 - q.1) (q.1 - r + 1) q.1 (by omega) b = 0 →
    P.first (adamsLongLayerToE1 unit X r hr p.1 p.2 a)
      (adamsJ unit X q.1 q.2 b) ∈
        adamsBoundaries unit X r hr (p.1 + q.1) (p.2 + q.2)

end
end KIP126.Classical.Adams
