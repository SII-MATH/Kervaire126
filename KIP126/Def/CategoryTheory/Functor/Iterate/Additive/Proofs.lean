module

public import KIP126.Def.CategoryTheory.Functor.Iterate
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Every actual finite iterate of an additive endofunctor is additive. -/
instance functorIterate_additive (F : C ⥤ C) [F.Additive] (n : ℕ) :
    (functorIterate F n).Additive := by
  induction n with
  | zero => exact inferInstanceAs (𝟭 C).Additive
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (functorIterate F n ⋙ F).Additive

end KIP126.Foundation
