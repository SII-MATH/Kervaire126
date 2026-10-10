import KIP126.Def.Algebra.GradedModule.Tensor.Raw.Data

/-! Monad and action laws for the prescribed left-tensor maps. -/

namespace KIP126.Algebra.GradedModule.LeftTensor

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem unit_naturality (A : Mon V) {X Y : V} (f : X ⟶ Y) :
    f ≫ unitApp A Y = unitApp A X ≫ (A.X ◁ f) := by
  sorry

theorem mul_naturality (A : Mon V) {X Y : V} (f : X ⟶ Y) :
    (A.X ◁ (A.X ◁ f)) ≫ mulApp A Y = mulApp A X ≫ (A.X ◁ f) := by
  sorry

theorem assoc (A : Mon V) (X : V) :
    (A.X ◁ mulApp A X) ≫ mulApp A X = mulApp A (A.X ⊗ X) ≫ mulApp A X := by
  sorry

theorem left_unit (A : Mon V) (X : V) :
    unitApp A (A.X ⊗ X) ≫ mulApp A X = 𝟙 (A.X ⊗ X) := by
  sorry

theorem right_unit (A : Mon V) (X : V) :
    (A.X ◁ unitApp A X) ≫ mulApp A X = 𝟙 (A.X ⊗ X) := by
  sorry

/-- The ordinary unital action equation gives the Eilenberg--Moore unit law. -/
theorem action_unit (A : Mon V) (X : V) (action : A.X ⊗ X ⟶ X)
    (h : (η[A.X] ▷ X) ≫ action = (λ_ X).hom) :
    unitApp A X ≫ action = 𝟙 X := by
  sorry

/-- The ordinary associative action equation gives the Eilenberg--Moore law. -/
theorem action_assoc (A : Mon V) (X : V) (action : A.X ⊗ X ⟶ X)
    (h : (μ[A.X] ▷ X) ≫ action =
      (α_ A.X A.X X).hom ≫ (A.X ◁ action) ≫ action) :
    mulApp A X ≫ action = (A.X ◁ action) ≫ action := by
  sorry

end KIP126.Algebra.GradedModule.LeftTensor
