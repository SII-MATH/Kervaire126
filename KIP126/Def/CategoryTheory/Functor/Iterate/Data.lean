module

public import Mathlib.CategoryTheory.Functor.Basic

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe u v

/-- Iteration of an actual endofunctor, with the last application on the right. -/
def functorIterate {C : Type u} [Category.{v} C] (F : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => functorIterate F n ⋙ F

end KIP126.Foundation
