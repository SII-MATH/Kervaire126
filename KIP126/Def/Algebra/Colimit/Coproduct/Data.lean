module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits
universe u

/-- The actual algebraic direct sum with its coordinate inclusions. -/
noncomputable def additiveDirectSumCofan {J : Type u} (A : J → AddCommGrpCat.{u}) : Cofan A := by
  classical
  exact Cofan.mk (AddCommGrpCat.of (DirectSum J (fun j => A j)))
    (fun j => AddCommGrpCat.ofHom (DirectSum.of (fun j => A j) j))

end KIP126.Foundation
