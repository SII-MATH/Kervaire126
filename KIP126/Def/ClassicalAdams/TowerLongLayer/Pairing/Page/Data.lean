import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Cycles.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)

/-- The induced bilinear pairing on the existing quotient pages. Its
existence is conditional on the supplied geometric pairing and predicates;
no new spectral sequence or unspecified page product is introduced. -/
def AdamsLongLayerPairing.onPage (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible) :
    adamsPage unit X r hr p.1 p.2 →ₗ[ℤ]
      adamsPage unit X r hr q.1 q.2 →ₗ[ℤ]
        adamsPage unit X r hr (p.1 + q.1) (p.2 + q.2) :=
  (P.cyclesToPage hP).liftQ₂
    (adamsCycleBoundaries unit X r hr p.1 p.2)
    (adamsCycleBoundaries unit X r hr q.1 q.2)
    (P.boundaries_le_left_ker hP hB) (P.boundaries_le_right_ker hP hB)

end
end KIP126.Classical.Adams
