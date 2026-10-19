module

public import KIP126.Def.Topology.HomotopyExtension.Proofs
public import Mathlib.CategoryTheory.LiftingProperties.Limits

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory CategoryTheory.Limits

universe u

/-- Actual homotopy extension is preserved by an actual topological pushout. -/
theorem hasHomotopyExtension_of_isPushout {A B C D : TopCat.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) (hf : HasHomotopyExtension f) :
    HasHomotopyExtension j := by
  apply (hasHomotopyExtension_iff_lifting j).mpr
  intro Y
  letI := (hasHomotopyExtension_iff_lifting f).mp hf Y
  exact h.flip.hasLiftingProperty (pathEvaluationZero Y)

end KIP126.Topology.HomotopyExtension
