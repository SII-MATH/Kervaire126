module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Source.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type} [Finite J]

@[simp, reassoc] theorem sourcePiLift_projection (X : J → Prespectrum.{u})
    {A : SourceCategory.{u}} (f : ∀ j, A ⟶ sourceLocalization.obj (X j)) (j : J) :
    sourcePiLift X f ≫ sourceLocalization.map (piProjection X j) = f j :=
  Fan.IsLimit.fac (sourceProductIsLimit X) f j

theorem sourcePi_hom_ext (X : J → Prespectrum.{u}) {A : SourceCategory.{u}}
    {f g : A ⟶ sourceLocalization.obj (piPrespectrum X)}
    (h : ∀ j, f ≫ sourceLocalization.map (piProjection X j) =
      g ≫ sourceLocalization.map (piProjection X j)) : f = g :=
  Fan.IsLimit.hom_ext (sourceProductIsLimit X) f g h

@[simp, reassoc] theorem sourcePiMap_projection {X Y : J → Prespectrum.{u}}
    (f : ∀ j, sourceLocalization.obj (X j) ⟶ sourceLocalization.obj (Y j)) (j : J) :
    sourcePiMap f ≫ sourceLocalization.map (piProjection Y j) =
      sourceLocalization.map (piProjection X j) ≫ f j :=
  sourcePiLift_projection Y _ j

@[simp] theorem sourcePiMap_id (X : J → Prespectrum.{u}) :
    sourcePiMap (fun j => 𝟙 (sourceLocalization.obj (X j))) = 𝟙 _ := by
  apply sourcePi_hom_ext X
  intro j
  simp

@[simp] theorem sourcePiMap_comp {X Y Z : J → Prespectrum.{u}}
    (f : ∀ j, sourceLocalization.obj (X j) ⟶ sourceLocalization.obj (Y j))
    (g : ∀ j, sourceLocalization.obj (Y j) ⟶ sourceLocalization.obj (Z j)) :
    sourcePiMap (fun j => f j ≫ g j) = sourcePiMap f ≫ sourcePiMap g := by
  apply sourcePi_hom_ext Z
  intro j
  simp only [Category.assoc, sourcePiMap_projection, sourcePiMap_projection_assoc]

@[simp] theorem sourcePiMap_map {X Y : J → Prespectrum.{u}} (f : ∀ j, X j ⟶ Y j) :
    sourcePiMap (fun j => sourceLocalization.map (f j)) =
      sourceLocalization.map (piMap f) := by
  apply sourcePi_hom_ext Y
  intro j
  rw [sourcePiMap_projection, ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The source pairing agrees with localization of the original strict pairing. -/
@[simp] theorem sourcePiLift_map (X : J → Prespectrum.{u}) {A : Prespectrum.{u}}
    (f : ∀ j, A ⟶ X j) :
    sourcePiLift X (fun j => sourceLocalization.map (f j)) = sourceLocalization.map (piLift f) := by
  apply sourcePi_hom_ext X
  intro j
  rw [sourcePiLift_projection, ← Functor.map_comp]
  rfl

@[reassoc] theorem comp_sourcePiLift (X : J → Prespectrum.{u})
    {A B : SourceCategory.{u}} (g : A ⟶ B)
    (f : ∀ j, B ⟶ sourceLocalization.obj (X j)) :
    g ≫ sourcePiLift X f = sourcePiLift X (fun j => g ≫ f j) := by
  apply sourcePi_hom_ext X
  intro j
  simp only [Category.assoc, sourcePiLift_projection]

@[reassoc] theorem sourcePiLift_comp_sourcePiMap {X Y : J → Prespectrum.{u}}
    (g : ∀ j, sourceLocalization.obj (X j) ⟶ sourceLocalization.obj (Y j))
    {A : SourceCategory.{u}} (f : ∀ j, A ⟶ sourceLocalization.obj (X j)) :
    sourcePiLift X f ≫ sourcePiMap g = sourcePiLift Y (fun j => f j ≫ g j) := by
  apply sourcePi_hom_ext Y
  intro j
  simp only [Category.assoc, sourcePiMap_projection, sourcePiLift_projection,
    sourcePiLift_projection_assoc]

@[reassoc] theorem sourcePiLift_map_comp {X Y : J → Prespectrum.{u}}
    (g : ∀ j, X j ⟶ Y j) {A : SourceCategory.{u}}
    (f : ∀ j, A ⟶ sourceLocalization.obj (X j)) :
    sourcePiLift X f ≫ sourceLocalization.map (piMap g) =
      sourcePiLift Y (fun j => f j ≫ sourceLocalization.map (g j)) := by
  apply sourcePi_hom_ext Y
  intro j
  rw [sourcePiLift_projection, Category.assoc, ← Functor.map_comp]
  have h : piMap g ≫ piProjection Y j = piProjection X j ≫ g j := rfl
  rw [h, Functor.map_comp, ← Category.assoc, sourcePiLift_projection]

end KIP126.StableHomotopy.Implementation.Prespectrum
