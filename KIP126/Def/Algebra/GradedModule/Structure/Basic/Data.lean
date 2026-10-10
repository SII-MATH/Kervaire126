import KIP126.Def.Algebra.GradedModule.Tensor.Linear.Proofs
import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
import Mathlib.CategoryTheory.Monad.Limits

/-!
The existing Eilenberg--Moore addition, ordinary scalar multiplication on
intertwining maps, and created finite limits and colimits for graded left
modules. No kernel, cokernel, or category structure is chosen by a placeholder.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u

noncomputable section

variable {K : Type u} [Field K] (A : Mon (GrVect K))

instance homSMul (X Y : LeftModule A) : SMul K (X ⟶ Y) where
  smul r f :=
    { f := r • f.f
      h := by
        calc
          (leftTensorMonad A).map (r • f.f) ≫ Y.a =
              (r • (leftTensorMonad A).map f.f) ≫ Y.a :=
            congrArg (· ≫ Y.a) (Functor.map_smul _ _ _)
          _ = r • ((leftTensorMonad A).map f.f ≫ Y.a) :=
            Linear.smul_comp _ _ _ _ _ _
          _ = r • (X.a ≫ f.f) := congrArg (r • ·) f.h
          _ = X.a ≫ (r • f.f) := (Linear.comp_smul _ _ _ _ _ _).symm }

/-- Forgetting the action is an injective additive map on morphisms. -/
def homForgetAddHom (X Y : LeftModule A) : (X ⟶ Y) →+ (X.A ⟶ Y.A) where
  toFun f := f.f
  map_zero' := rfl
  map_add' _ _ := rfl

instance homModule (X Y : LeftModule A) : Module K (X ⟶ Y) :=
  Function.Injective.module K (homForgetAddHom A X Y)
    (fun _ _ h => Monad.Algebra.Hom.ext h) (fun _ _ => rfl)

instance linear : Linear K (LeftModule A) where
  homModule := homModule A
  smul_comp _ _ _ r f g := by
    apply Monad.Algebra.Hom.ext
    change (r • f.f) ≫ g.f = r • (f.f ≫ g.f)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ f r g := by
    apply Monad.Algebra.Hom.ext
    change f.f ≫ (r • g.f) = r • (f.f ≫ g.f)
    exact Linear.comp_smul _ _ _ _ _ _

instance forget_linear : Functor.Linear K (forget A) where
  map_smul _ _ := rfl

instance hasFiniteLimits : HasFiniteLimits (LeftModule A) where
  out _ :=
    { has_limit F := Monad.hasLimit_of_comp_forget_hasLimit F }

instance hasFiniteColimits : HasFiniteColimits (LeftModule A) where
  out _ :=
    { has_colimit F := Monad.forget_creates_colimits_of_monad_preserves F }

end

end KIP126.Algebra.GradedModule
