import KIP126.Def.Algebra.GradedModule.Tensor.Raw.Proofs

/-!
The actual left-tensor monad of a monoid and its category of left modules.
An object has its given action `A ⊗ X → X`; maps are the ordinary maps
intertwining those actions. No replacement category or action is selected.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

namespace LeftTensor

/-- The unit natural transformation on the actual left-tensor functor. -/
def unit (A : Mon V) : 𝟭 V ⟶ tensorLeft A.X where
  app := unitApp A
  naturality _ _ f := unit_naturality A f

/-- The multiplication natural transformation on the same left-tensor functor. -/
def multiplication (A : Mon V) : tensorLeft A.X ⋙ tensorLeft A.X ⟶ tensorLeft A.X where
  app := mulApp A
  naturality _ _ f := mul_naturality A f

end LeftTensor

/-- The monad `X ↦ A ⊗ X`, using the actual monoid unit and multiplication. -/
def leftTensorMonad (A : Mon V) : Monad V where
  toFunctor := tensorLeft A.X
  «η» := LeftTensor.unit A
  «μ» := LeftTensor.multiplication A
  assoc := LeftTensor.assoc A
  left_unit := LeftTensor.left_unit A
  right_unit := LeftTensor.right_unit A

/-- Actual left modules, as algebras over the specified tensor monad. -/
abbrev LeftModule (A : Mon V) := Monad.Algebra (leftTensorMonad A)

/-- Forget the action, keeping the underlying object and morphism. -/
def forget (A : Mon V) : LeftModule A ⥤ V :=
  Monad.forget (leftTensorMonad A)

/-- Build a left module from its actual action and the usual monoidal laws. -/
def ofAction (A : Mon V) (X : V) (action : A.X ⊗ X ⟶ X)
    (unit : (η[A.X] ▷ X) ≫ action = (λ_ X).hom)
    (assoc : (μ[A.X] ▷ X) ≫ action =
      (α_ A.X A.X X).hom ≫ (A.X ◁ action) ≫ action) : LeftModule A where
  A := X
  a := action
  unit := LeftTensor.action_unit A X action unit
  assoc := LeftTensor.action_assoc A X action assoc

end KIP126.Algebra.GradedModule
