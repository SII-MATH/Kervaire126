module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

@[simp] theorem sourceStableHomotopyAddFunctor_fac (d : ℤ) :
    sourceLocalization ⋙ sourceStableHomotopyAddFunctor.{u} d =
      Prespectrum.stableHomotopyAddFunctor d :=
  Localization.Construction.fac _ _

@[simp] theorem sourceStableHomotopyAddFunctor_map {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) :
    (sourceStableHomotopyAddFunctor d).map (sourceLocalization.map f) =
      AddCommGrpCat.ofHom (Prespectrum.stableHomotopyAddHom f d) := by
  have h : ∀ (F G : Prespectrum.{u} ⥤ AddCommGrpCat.{u}),
      F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (h _ _ (sourceStableHomotopyAddFunctor_fac d))

/-- Forgetting the constructed group operations recovers the original
stable-set functor on every localized morphism. -/
theorem sourceStableHomotopyAddFunctor_forget (d : ℤ) :
    sourceStableHomotopyAddFunctor.{u} d ⋙ forget AddCommGrpCat =
      sourceStableHomotopyFunctor d := by
  apply Localization.Construction.uniq _ _
  rw [← Functor.assoc, sourceStableHomotopyAddFunctor_fac, sourceStableHomotopyFunctor_fac]
  rfl

theorem sourceStableHomotopyAddFunctor_forget_map {X Y : Prespectrum.{u}}
    (f : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) (d : ℤ) :
    (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor d).map f) =
      (sourceStableHomotopyFunctor d).map f := by
  have h : ∀ (F G : SourceCategory.{u} ⥤ Type u),
      F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (h (sourceStableHomotopyAddFunctor d ⋙ forget AddCommGrpCat)
    (sourceStableHomotopyFunctor d) (sourceStableHomotopyAddFunctor_forget d))

end KIP126.StableHomotopy.Implementation
