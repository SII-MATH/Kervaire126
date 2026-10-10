import KIP126.Def.StableHomotopy.Context.Mapping.Composition.Data

namespace KIP126.StableHomotopy.Mapping

open CategoryTheory MonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- The chosen internal composition is precisely successive evaluation under
adjunction, including the required associator. -/
theorem uncurry_composition (X Y Z : C) :
    MonoidalClosed.uncurry (composition X Y Z) =
      (α_ X (object X Y) (object Y Z)).inv ≫
        (ihom.ev X).app Y ▷ object Y Z ≫ (ihom.ev Y).app Z :=
  MonoidalClosed.uncurry_curry _

set_option backward.isDefEq.respectTransparency false in
/-- Composition also agrees with evaluation for arbitrary parametrizing
objects, including sphere parameters used for graded homotopy classes. -/
theorem uncurry_tensor_composition {X Y Z A B : C}
    (f : A ⟶ object X Y) (g : B ⟶ object Y Z) :
    MonoidalClosed.uncurry ((f ⊗ₘ g) ≫ composition X Y Z) =
      (α_ X A B).inv ≫ MonoidalClosed.uncurry f ▷ B ≫
        MonoidalClosed.uncurry g := by
  rw [MonoidalClosed.uncurry_natural_left, uncurry_composition]
  simp only [MonoidalClosed.uncurry_eq, tensorHom_def, whiskerLeft_comp,
    comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_right_assoc,
    associator_inv_naturality_middle_assoc, whisker_exchange_assoc]
  rfl

@[reassoc (attr := simp)]
theorem identity_composition (X Y : C) :
    (λ_ (object X Y)).inv ≫ identity X ▷ object X Y ≫ composition X X Y = 𝟙 _ :=
  MonoidalClosed.id_comp X Y

@[reassoc (attr := simp)]
theorem composition_identity (X Y : C) :
    (ρ_ (object X Y)).inv ≫ object X Y ◁ identity Y ≫ composition X Y Y = 𝟙 _ :=
  MonoidalClosed.comp_id X Y

@[reassoc]
theorem composition_assoc (W X Y Z : C) :
    (α_ (object W X) (object X Y) (object Y Z)).inv ≫
        composition W X Y ▷ object Y Z ≫ composition W Y Z =
      object W X ◁ composition X Y Z ≫ composition W X Z :=
  MonoidalClosed.assoc W X Y Z

@[simp] theorem name_identity (X : C) : name (𝟙 X) = identity X :=
  MonoidalClosed.curry'_id X

/-- Composition agrees with actual maps, not just with abstract pointwise
operations chosen on the mapping object. -/
@[simp] theorem composeNames_name {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    composeNames (name f) (name g) = name (f ≫ g) :=
  (MonoidalClosed.curry'_comp f g).symm

/-- The same formula for arbitrary internal names follows from the adjunction
equivalence and therefore does not impose an extra input condition. -/
theorem composeNames_actual {X Y Z : C} (f : 𝟙_ C ⟶ object X Y)
    (g : 𝟙_ C ⟶ object Y Z) :
    (nameEquiv X Z).symm (composeNames f g) =
      (nameEquiv X Y).symm f ≫ (nameEquiv Y Z).symm g := by
  change MonoidalClosed.uncurry' (composeNames f g) =
    MonoidalClosed.uncurry' f ≫ MonoidalClosed.uncurry' g
  apply MonoidalClosed.curry'_injective
  rw [MonoidalClosed.curry'_uncurry', MonoidalClosed.curry'_comp,
    MonoidalClosed.curry'_uncurry', MonoidalClosed.curry'_uncurry']
  rfl

end KIP126.StableHomotopy.Mapping
