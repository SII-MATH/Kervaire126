import KIP126.Def.Algebra.GradedModule.Tensor.Raw.Data

/-! Monad and action laws for the prescribed left-tensor maps. -/

namespace KIP126.Algebra.GradedModule.LeftTensor

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem unit_naturality (A : Mon V) {X Y : V} (f : X ⟶ Y) :
    f ≫ unitApp A Y = unitApp A X ≫ (A.X ◁ f) := by
  dsimp [unitApp]
  rw [Category.assoc, leftUnitor_inv_naturality_assoc, whisker_exchange]

theorem mul_naturality (A : Mon V) {X Y : V} (f : X ⟶ Y) :
    (A.X ◁ (A.X ◁ f)) ≫ mulApp A Y = mulApp A X ≫ (A.X ◁ f) := by
  dsimp [mulApp]
  rw [Category.assoc, associator_inv_naturality_right_assoc, whisker_exchange]

theorem assoc (A : Mon V) (X : V) :
    (A.X ◁ mulApp A X) ≫ mulApp A X = mulApp A (A.X ⊗ X) ≫ mulApp A X := by
  simp only [mulApp, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight, MonObj.mul_assoc_flip]
  simp only [comp_whiskerRight, pentagon_inv_assoc]
  simp

theorem left_unit (A : Mon V) (X : V) :
    unitApp A (A.X ⊗ X) ≫ mulApp A X = 𝟙 (A.X ⊗ X) := by
  simp only [unitApp, mulApp, Category.assoc, associator_inv_naturality_left_assoc]
  rw [← Category.assoc, ← leftUnitor_inv_whiskerRight]
  rw [← comp_whiskerRight, MonObj.one_mul]
  simp

theorem right_unit (A : Mon V) (X : V) :
    (A.X ◁ unitApp A X) ≫ mulApp A X = 𝟙 (A.X ⊗ X) := by
  simp only [unitApp, mulApp, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← Category.assoc,
    triangle_assoc_comp_left_inv]
  rw [← comp_whiskerRight, MonObj.mul_one]
  simp

/-- The ordinary unital action equation gives the Eilenberg--Moore unit law. -/
theorem action_unit (A : Mon V) (X : V) (action : A.X ⊗ X ⟶ X)
    (h : (η[A.X] ▷ X) ≫ action = (λ_ X).hom) :
    unitApp A X ≫ action = 𝟙 X := by
  simp [unitApp, Category.assoc, h]

/-- The ordinary associative action equation gives the Eilenberg--Moore law. -/
theorem action_assoc (A : Mon V) (X : V) (action : A.X ⊗ X ⟶ X)
    (h : (μ[A.X] ▷ X) ≫ action =
      (α_ A.X A.X X).hom ≫ (A.X ◁ action) ≫ action) :
    mulApp A X ≫ action = (A.X ◁ action) ≫ action := by
  simp [mulApp, Category.assoc, h]

end KIP126.Algebra.GradedModule.LeftTensor
