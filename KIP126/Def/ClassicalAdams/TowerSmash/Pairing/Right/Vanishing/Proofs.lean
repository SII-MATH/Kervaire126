import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Transport.Proofs
import KIP126.Def.ClassicalAdams.TowerLayer.Mapping.Proofs
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- Both one-factor eliminations have the same composite to the sphere,
without any vanishing or ring hypothesis. -/
theorem unitFiberInclusion_postcomp_eq :
    ((fiberι unit ▷ fiber unit) ≫ (λ_ (fiber unit)).hom) ≫ fiberι unit =
      ((fiber unit ◁ fiberι unit) ≫ (ρ_ (fiber unit)).hom) ≫ fiberι unit := by
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← rightUnitor_naturality,
    unitors_equal, whisker_exchange_assoc]

/-- The two-factor condition follows from vanishing of maps into the
desuspended coefficient object. This uses the actual fiber triangle, not
an assumed compatibility of the two elimination maps. -/
theorem unitFiberInclusionCommutes_of_vanishing
    (hvan : ∀ a : fiber unit ⊗ fiber unit ⟶ H⟦(-1 : ℤ)⟧, a = 0) :
    UnitFiberInclusionCommutes unit := by
  apply fiberι_postcomp_injective_of_vanishing unit hvan
  exact unitFiberInclusion_postcomp_eq unit

variable [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

/-- The right-input law on the existing tower now needs only the stated
mapping-group vanishing, besides the explicit tensor comparison structures. -/
theorem adamsTowerSpherePairingIso_step_right_of_vanishing
    (hvan : ∀ a : fiber unit ⊗ fiber unit ⟶ H⟦(-1 : ℤ)⟧, a = 0) (s t : ℕ) :
    adamsTowerSpherePairingNextRight unit s t ≫
        adamsTowerStep unit (𝟙_ C) (t + s) =
      (adamsTower unit (𝟙_ C) s ◁ adamsTowerStep unit (𝟙_ C) t) ≫
        (adamsTowerSpherePairingIso unit s t).hom :=
  adamsTowerSpherePairingIso_step_right unit
    (unitFiberInclusionCommutes_of_vanishing unit hvan) s t

end KIP126.Classical.Adams
