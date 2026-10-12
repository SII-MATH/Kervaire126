module

public import KIP126.Def.CategoryTheory.Functor.Iterate.Data
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C]

@[simp] theorem functorIterate_zero (F : C ⥤ C) : functorIterate F 0 = 𝟭 C := rfl

@[simp] theorem functorIterate_one (F : C ⥤ C) : functorIterate F 1 = F := rfl

theorem functorIterate_succ (F : C ⥤ C) (n : ℕ) :
    functorIterate F (n + 1) = functorIterate F n ⋙ F := rfl

/-- The full nonnegative composition law holds as equality of actual functors. -/
theorem functorIterate_add (F : C ⥤ C) (m n : ℕ) :
    functorIterate F (m + n) = functorIterate F m ⋙ functorIterate F n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change functorIterate F (m + n) ⋙ F = (functorIterate F m ⋙ functorIterate F n) ⋙ F
    rw [ih]

theorem functorIterate_obj (F : C ⥤ C) (n : ℕ) (X : C) :
    (functorIterate F n).obj X = (F.obj^[n]) X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F.obj ((functorIterate F n).obj X) = (F.obj^[n + 1]) X
    rw [Function.iterate_succ_apply', ih]

/-- Strict compatibility with one step gives strict compatibility with
every nonnegative iterate. -/
theorem functorIterate_comp {D : Type u'} [Category.{v'} D]
    (F : C ⥤ C) (G : D ⥤ D) (H : C ⥤ D) (h : F ⋙ H = H ⋙ G) (n : ℕ) :
    functorIterate F n ⋙ H = H ⋙ functorIterate G n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change functorIterate F n ⋙ (F ⋙ H) = (H ⋙ functorIterate G n) ⋙ G
    rw [h]
    exact congrArg (fun K => K ⋙ G) ih

end KIP126.Foundation
