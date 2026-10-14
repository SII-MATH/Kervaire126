module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Universal.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual Moore map is the unique extension across the same
constructed unit into the already constructed Moore target. -/
noncomputable def sourceMooreCompletionMap (p : ℕ) {X Y : SourceCategory.{u}} (f : X ⟶ Y) :
    sourceMooreCompletion p X ⟶ sourceMooreCompletion p Y :=
  ((sourceMooreCompletionUnit_precomp_bijective p X (sourceMooreCompletion p Y)
    (fun U hU => by
      letI := hU
      exact sourceMooreCompletion_hom_subsingleton p Y U)).surjective
    (f ≫ sourceMooreCompletionUnit p Y)).choose

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Maps between the actual Moore objects are determined by restriction
along the original constructed unit. -/
theorem sourceMooreCompletion_hom_ext (p : ℕ) {X Y : SourceCategory.{u}}
    {a b : sourceMooreCompletion p X ⟶ sourceMooreCompletion p Y}
    (h : sourceMooreCompletionUnit p X ≫ a = sourceMooreCompletionUnit p X ≫ b) : a = b :=
  (sourceMooreCompletionUnit_precomp_bijective p X (sourceMooreCompletion p Y)
    (fun U hU => by
      letI := hU
      exact sourceMooreCompletion_hom_subsingleton p Y U)).injective h

/-- The chosen extension makes the same Moore unit natural. -/
theorem sourceMooreCompletionMap_unit (p : ℕ) {X Y : SourceCategory.{u}} (f : X ⟶ Y) :
    sourceMooreCompletionUnit p X ≫ sourceMooreCompletionMap p f =
      f ≫ sourceMooreCompletionUnit p Y :=
  ((sourceMooreCompletionUnit_precomp_bijective p X (sourceMooreCompletion p Y)
    (fun U hU => by
      letI := hU
      exact sourceMooreCompletion_hom_subsingleton p Y U)).surjective
    (f ≫ sourceMooreCompletionUnit p Y)).choose_spec

@[simp] theorem sourceMooreCompletionMap_id (p : ℕ) (X : SourceCategory.{u}) :
    sourceMooreCompletionMap p (𝟙 X) = 𝟙 (sourceMooreCompletion p X) := by
  apply sourceMooreCompletion_hom_ext p
  rw [sourceMooreCompletionMap_unit, Category.id_comp, Category.comp_id]

@[simp] theorem sourceMooreCompletionMap_comp (p : ℕ) {X Y Z : SourceCategory.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourceMooreCompletionMap p (f ≫ g) = sourceMooreCompletionMap p f ≫
      sourceMooreCompletionMap p g := by
  apply sourceMooreCompletion_hom_ext p
  rw [sourceMooreCompletionMap_unit, ← Category.assoc, sourceMooreCompletionMap_unit]
  simp only [Category.assoc, sourceMooreCompletionMap_unit]

@[simp] theorem sourceMooreCompletionMap_zero (p : ℕ) (X Y : SourceCategory.{u}) :
    sourceMooreCompletionMap p (0 : X ⟶ Y) = 0 := by
  apply sourceMooreCompletion_hom_ext p
  rw [sourceMooreCompletionMap_unit, Limits.zero_comp, Limits.comp_zero]

/-- Additivity follows from unique extension, without any coherence
assumption on the cofiber choices used to build the tower. -/
@[simp] theorem sourceMooreCompletionMap_add (p : ℕ) {X Y : SourceCategory.{u}}
    (f g : X ⟶ Y) :
    sourceMooreCompletionMap p (f+g) = sourceMooreCompletionMap p f +
      sourceMooreCompletionMap p g := by
  apply sourceMooreCompletion_hom_ext p
  rw [sourceMooreCompletionMap_unit, Preadditive.comp_add,
    sourceMooreCompletionMap_unit, sourceMooreCompletionMap_unit, Preadditive.add_comp]

end KIP126.StableHomotopy.Implementation

end
