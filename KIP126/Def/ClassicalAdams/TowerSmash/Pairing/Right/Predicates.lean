import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Data

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- The two maps `bar H ⊗ bar H → bar H` obtained by applying the actual
unit-fiber inclusion to either factor agree. This is a lower compatibility
condition, not an axiom, not provided by tensor exactness alone in this API,
and not a claim of coherent multiplicativity or a spectral-sequence Leibniz law. -/
def UnitFiberInclusionCommutes : Prop :=
  (fiberι unit ▷ fiber unit) ≫ (λ_ (fiber unit)).hom =
    (fiber unit ◁ fiberι unit) ≫ (ρ_ (fiber unit)).hom

end KIP126.Classical.Adams
