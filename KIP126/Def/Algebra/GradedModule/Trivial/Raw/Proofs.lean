import KIP126.Def.Algebra.GradedModule.Trivial.Raw.Data

/-! Unit and associativity of restriction along the specified augmentation. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u v
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem trivialAction_unit {A : Mon V} (ε : Augmentation A) (X : V) :
    (η[A.X] ▷ X) ≫ trivialAction ε X = (λ_ X).hom := by
  sorry

theorem trivialAction_assoc {A : Mon V} (ε : Augmentation A) (X : V) :
    (μ[A.X] ▷ X) ≫ trivialAction ε X =
      (α_ A.X A.X X).hom ≫ (A.X ◁ trivialAction ε X) ≫ trivialAction ε X := by
  sorry

end KIP126.Algebra.GradedModule
