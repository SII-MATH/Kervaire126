module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

@[simp] theorem homotopyPullbackPath_zero {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullbackPath f g ≫ pathEvaluation Y 0 = homotopyPullbackFst f g ≫ f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  exact p.val.1.property

@[simp] theorem homotopyPullbackPath_one {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullbackPath f g ≫ pathEvaluation Y 1 = homotopyPullbackSnd f g ≫ g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  exact p.property

@[simp, reassoc] theorem homotopyPullbackLift_fst {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z)
    (H : A ⟶ pathPrespectrum Y) (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = b ≫ g) :
    homotopyPullbackLift a b H h₀ h₁ ≫ homotopyPullbackFst f g = a := rfl

@[simp, reassoc] theorem homotopyPullbackLift_snd {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z)
    (H : A ⟶ pathPrespectrum Y) (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = b ≫ g) :
    homotopyPullbackLift a b H h₀ h₁ ≫ homotopyPullbackSnd f g = b := rfl

@[simp, reassoc] theorem homotopyPullbackLift_path {A X Y Z : Prespectrum.{u}}
    {f : X ⟶ Y} {g : Z ⟶ Y} (a : A ⟶ X) (b : A ⟶ Z)
    (H : A ⟶ pathPrespectrum Y) (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = b ≫ g) :
    homotopyPullbackLift a b H h₀ h₁ ≫ homotopyPullbackPath f g = H := rfl

/-- The two projections and the retained homotopy determine the strict lift. -/
theorem homotopyPullbackHom_ext {A X Y Z : Prespectrum.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    (a b : A ⟶ homotopyPullback f g)
    (hX : a ≫ homotopyPullbackFst f g = b ≫ homotopyPullbackFst f g)
    (hZ : a ≫ homotopyPullbackSnd f g = b ≫ homotopyPullbackSnd f g)
    (hH : a ≫ homotopyPullbackPath f g = b ≫ homotopyPullbackPath f g) : a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) ?_
  · exact congrArg (fun k : A ⟶ X => k.level n x) hX
  · exact congrArg (fun k : A ⟶ pathPrespectrum Y => k.level n x) hH
  · exact congrArg (fun k : A ⟶ Z => k.level n x) hZ

/-- The actual retained homotopy makes the original square commute after
ordinary stable localization. -/
theorem source_homotopyPullback_comm {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    sourceLocalization.map (homotopyPullbackFst f g) ≫ sourceLocalization.map f =
      sourceLocalization.map (homotopyPullbackSnd f g) ≫ sourceLocalization.map g := by
  rw [← CategoryTheory.Functor.map_comp, ← homotopyPullbackPath_zero,
    CategoryTheory.Functor.map_comp, source_pathEvaluation_eq Y 0 1,
    ← CategoryTheory.Functor.map_comp, homotopyPullbackPath_one,
    CategoryTheory.Functor.map_comp]

end KIP126.StableHomotopy.Implementation.Prespectrum
