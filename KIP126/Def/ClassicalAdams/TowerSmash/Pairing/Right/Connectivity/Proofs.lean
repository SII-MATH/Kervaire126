import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Vanishing.Proofs
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)

/-- In the cohomological indexing used by Mathlib, connective spectra are
`≤ 0`, and desuspending a `≥ 0` coefficient object gives a `≥ 1` object.
This theorem does not choose a t-structure for the fixed foundation. -/
theorem unitFiber_mapping_vanishing_of_tStructure (t : Triangulated.TStructure C)
    [t.IsLE (fiber unit ⊗ fiber unit) 0] [t.IsGE H 0]
    (a : fiber unit ⊗ fiber unit ⟶ H⟦(-1 : ℤ)⟧) : a = 0 := by
  letI := t.isGE_shift H 0 (-1) 1 (by decide)
  exact t.zero a 0 1

/-- The two-factor equality is derived from connective tensor closure and
t-structure orthogonality. Connectivity and the t-structure are explicit
lower hypotheses, not properties inferred from the current HF2 interface. -/
theorem unitFiberInclusionCommutes_of_tStructure (t : Triangulated.TStructure C)
    (htensor : ∀ X Y : C, t.IsLE X 0 → t.IsLE Y 0 → t.IsLE (X ⊗ Y) 0)
    [t.IsLE (fiber unit) 0] [t.IsGE H 0] : UnitFiberInclusionCommutes unit := by
  letI := htensor (fiber unit) (fiber unit) inferInstance inferInstance
  exact unitFiberInclusionCommutes_of_vanishing unit
    (unitFiber_mapping_vanishing_of_tStructure unit t)

variable [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

/-- The actual sphere tower's right-input compatibility follows from the
explicit t-structure and tensor conditions, without assuming that equality. -/
theorem adamsTowerSpherePairingIso_step_right_of_tStructure
    (t : Triangulated.TStructure C)
    (htensor : ∀ X Y : C, t.IsLE X 0 → t.IsLE Y 0 → t.IsLE (X ⊗ Y) 0)
    [t.IsLE (fiber unit) 0] [t.IsGE H 0] (s q : ℕ) :
    adamsTowerSpherePairingNextRight unit s q ≫
        adamsTowerStep unit (𝟙_ C) (q + s) =
      (adamsTower unit (𝟙_ C) s ◁ adamsTowerStep unit (𝟙_ C) q) ≫
        (adamsTowerSpherePairingIso unit s q).hom :=
  adamsTowerSpherePairingIso_step_right unit
    (unitFiberInclusionCommutes_of_tStructure unit t htensor) s q

end KIP126.Classical.Adams
