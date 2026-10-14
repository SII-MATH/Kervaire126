module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Group.Int.Defs

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A chain indexed by all integers, with invertible comparison between
one specified endofunctor and each forward step. -/
structure IntegerChain (F : C ⥤ C) where
  obj : ℤ → C
  step : ∀ n, F.obj (obj n) ≅ obj (n + 1)

namespace IntegerChain

variable {F : C ⥤ C}

@[ext] structure Hom (X Y : IntegerChain F) where
  app : ∀ n, X.obj n ⟶ Y.obj n
  comm : ∀ n, F.map (app n) ≫ (Y.step n).hom = (X.step n).hom ≫ app (n + 1)

instance : Category (IntegerChain F) where
  Hom X Y := Hom X Y
  id X := ⟨fun _ => 𝟙 _, by intro n; simp⟩
  comp f g := ⟨fun n => f.app n ≫ g.app n, by
    intro n
    rw [Functor.map_comp, Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp f := Hom.ext (by funext n; exact Category.id_comp _)
  comp_id f := Hom.ext (by funext n; exact Category.comp_id _)
  assoc f g h := Hom.ext (by funext n; exact Category.assoc _ _ _)

/-- Evaluation at a specified integer degree. -/
def eval (F : C ⥤ C) (n : ℤ) : IntegerChain F ⥤ C where
  obj X := X.obj n
  map f := f.app n

end IntegerChain
end KIP126.Foundation
