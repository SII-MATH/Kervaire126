import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Triangulated.Functor
import KIPBase.StableHomotopy.MonoidalModelCategory

/-!
# Abstract stable model categories

This module records stability entirely at the level of an arbitrary model
category and its localization. It contains no point-set topology, cylinder
construction, or CGWH-specific assumption.
-/

universe v u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace KIPBase.StableHomotopy

variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-! ## Homotopy category -/

/-- The localization of a model category at its weak equivalences. -/
abbrev Ho : Type _ := (weakEquivalences C).Localization

/-- The canonical functor from a model category to its homotopy category. -/
abbrev hoCat : C ⥤ Ho C := (weakEquivalences C).Q

/-! ## Homotopy pushouts and pullbacks -/

/-- A square in `Ho(C)` is a homotopy pushout square when it is isomorphic to
a point-set pushout square whose left edge is a cofibration. -/
def isHoPushoutSquare [HasPushouts C]
    {X Y Z W : Ho C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W)
    (_sq : f ≫ h = g ≫ k) : Prop :=
  ∃ (A B C' D : C) (f' : A ⟶ B) (g' : A ⟶ C')
    (h' : B ⟶ D) (k' : C' ⟶ D),
    (cofibrations C) f' ∧ IsPushout f' g' h' k' ∧
    ∃ (iX : (hoCat C).obj A ≅ X) (iY : (hoCat C).obj B ≅ Y)
      (iZ : (hoCat C).obj C' ≅ Z) (iW : (hoCat C).obj D ≅ W),
      iX.hom ≫ f = (hoCat C).map f' ≫ iY.hom ∧
      iX.hom ≫ g = (hoCat C).map g' ≫ iZ.hom ∧
      iY.hom ≫ h = (hoCat C).map h' ≫ iW.hom ∧
      iZ.hom ≫ k = (hoCat C).map k' ≫ iW.hom

/-- A square in `Ho(C)` is a homotopy pullback square when it is isomorphic to
a point-set pullback square whose right edge is a fibration. -/
def isHoPullbackSquare [HasPullbacks C]
    {X Y Z W : Ho C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W)
    (_sq : f ≫ h = g ≫ k) : Prop :=
  ∃ (A B C' D : C) (f' : A ⟶ B) (g' : A ⟶ C')
    (h' : B ⟶ D) (k' : C' ⟶ D),
    (fibrations C) h' ∧ IsPullback f' g' h' k' ∧
    ∃ (iX : (hoCat C).obj A ≅ X) (iY : (hoCat C).obj B ≅ Y)
      (iZ : (hoCat C).obj C' ≅ Z) (iW : (hoCat C).obj D ≅ W),
      iX.hom ≫ f = (hoCat C).map f' ≫ iY.hom ∧
      iX.hom ≫ g = (hoCat C).map g' ≫ iZ.hom ∧
      iY.hom ≫ h = (hoCat C).map h' ≫ iW.hom ∧
      iZ.hom ≫ k = (hoCat C).map k' ≫ iW.hom

/-! ## Stability -/

/-- A model category is stable when its derived suspension and loop functors
are inverse equivalences. The square comparison fields record the equivalent
homotopy pushout/pullback behavior and the point-set comparison maps used in
applications. -/
class IsStableModelCategory extends Preadditive (Ho C) where
  /-- The homotopy category has a zero object. -/
  homotopyHasZeroObject : HasZeroObject (Ho C)
  /-- The derived suspension determines the integer shift on the homotopy
  category. -/
  homotopyShift : HasShift (Ho C) ℤ
  /-- Every shift on the homotopy category is additive. -/
  homotopyShiftAdditive : ∀ n : ℤ,
    @Functor.Additive (Ho C) (Ho C) _ _ _ _ (shiftFunctor (Ho C) n)
  /-- The homotopy category carries its triangulated structure. This is the
  triangulation produced by the stable model structure. -/
  homotopyPretriangulated :
    @Pretriangulated (Ho C) _ homotopyHasZeroObject homotopyShift
      inferInstance homotopyShiftAdditive
  /-- Derived suspension on the homotopy category. -/
  suspension : Ho C ⥤ Ho C
  /-- Derived loop functor on the homotopy category. -/
  loop : Ho C ⥤ Ho C
  /-- The derived suspension is left adjoint to the derived loop functor. -/
  adj : suspension ⊣ loop
  /-- Derived suspension is additive. -/
  suspension_additive : suspension.Additive
  /-- The unit of the suspension-loop adjunction is an isomorphism. -/
  unit_isIso : ∀ X : Ho C, IsIso (adj.unit.app X)
  /-- The counit of the suspension-loop adjunction is an isomorphism. -/
  counit_isIso : ∀ X : Ho C, IsIso (adj.counit.app X)
  /-- Homotopy pushout squares and homotopy pullback squares coincide. -/
  bicartesian_iff {X Y Z W : Ho C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W)
    (sq : f ≫ h = g ≫ k) :
    isHoPushoutSquare C f g h k sq ↔ isHoPullbackSquare C f g h k sq
  /-- A fibrant point-set pullback computes the corresponding homotopy
  pullback. -/
  pullbackComparison_isIso {A B C' D : C}
    (f : A ⟶ B) (g : A ⟶ C') (h : B ⟶ D) (k : C' ⟶ D)
    (sq : f ≫ h = g ≫ k) (hh : (fibrations C) h)
    (hpb : isHoPullbackSquare C
      ((hoCat C).map f) ((hoCat C).map g)
      ((hoCat C).map h) ((hoCat C).map k)
      (by rw [← Functor.map_comp, sq, Functor.map_comp])) :
    IsIso ((hoCat C).map (pullback.lift f g sq))
  /-- A cofibrant point-set pushout computes the corresponding homotopy
  pushout. -/
  pushoutComparison_isIso {A B C' D : C}
    (f : A ⟶ B) (g : A ⟶ C') (h : B ⟶ D) (k : C' ⟶ D)
    (sq : f ≫ h = g ≫ k) (hf : (cofibrations C) f)
    (hpo : isHoPushoutSquare C
      ((hoCat C).map f) ((hoCat C).map g)
      ((hoCat C).map h) ((hoCat C).map k)
      (by rw [← Functor.map_comp, sq, Functor.map_comp])) :
    IsIso ((hoCat C).map (pushout.desc h k sq))

namespace IsStableModelCategory

variable [IsStableModelCategory C]

attribute [instance] IsStableModelCategory.homotopyHasZeroObject
  IsStableModelCategory.homotopyShift IsStableModelCategory.homotopyShiftAdditive
  IsStableModelCategory.homotopyPretriangulated

instance (X : Ho C) : IsIso ((IsStableModelCategory.adj (C := C)).unit.app X) :=
  IsStableModelCategory.unit_isIso (C := C) X

instance (X : Ho C) : IsIso ((IsStableModelCategory.adj (C := C)).counit.app X) :=
  IsStableModelCategory.counit_isIso (C := C) X

/-- The suspension-loop adjunction induces an equivalence of the homotopy
category. -/
noncomputable def suspensionLoopEquivalence : Ho C ≌ Ho C :=
  Adjunction.toEquivalence (IsStableModelCategory.adj (C := C))

noncomputable instance :
    (IsStableModelCategory.suspension (C := C)).IsEquivalence :=
  (suspensionLoopEquivalence C).isEquivalence_functor

noncomputable instance :
    (IsStableModelCategory.loop (C := C)).IsEquivalence :=
  (suspensionLoopEquivalence C).isEquivalence_inverse

end IsStableModelCategory

/-! ## Stable symmetric monoidal model categories -/

/-- A stable symmetric monoidal model category combines a stable model
structure with a compatible closed symmetric monoidal model structure. The
monoid axiom remains a separate optional assumption. -/
class StableMonoidalCategory
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [HasLimits C] [HasColimits C] [HasPushouts C] [HasInitial C]
    [HasZeroMorphisms C] [HasZeroObject C]
    extends SymMonoidalModelCategory C, IsStableModelCategory C

end KIPBase.StableHomotopy
