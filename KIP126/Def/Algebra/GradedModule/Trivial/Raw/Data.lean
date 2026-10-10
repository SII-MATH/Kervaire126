import KIP126.Def.Algebra.GradedModule.Tensor.Data

/-! The trivial left action is restriction along an actual augmentation.
Its underlying object and action are specified before their laws. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory

universe u v
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- An augmentation is a morphism to the canonical unit algebra. -/
abbrev Augmentation (A : Mon V) := A ⟶ Mon.trivial V

/-- Restrict the tensor-unit action along the given algebra augmentation. -/
def trivialAction {A : Mon V} (ε : Augmentation A) (X : V) : A.X ⊗ X ⟶ X :=
  (ε.hom ▷ X) ≫ (λ_ X).hom

end KIP126.Algebra.GradedModule
