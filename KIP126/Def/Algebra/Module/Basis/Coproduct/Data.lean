module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

namespace KIP126.Foundation
open CategoryTheory CategoryTheory.Limits
universe u

/-- The additive cofan given by the scalar lines of an actual module basis. -/
noncomputable def basisAdditiveCofan {R V J : Type u} [Ring R]
    [AddCommGroup V] [Module R V] (b : Module.Basis J R V) :
    Cofan (fun _ : J => AddCommGrpCat.of R) :=
  Cofan.mk (AddCommGrpCat.of V) (fun j => AddCommGrpCat.ofHom {
    toFun := fun c => c • b j
    map_zero' := zero_smul R (b j)
    map_add' := fun c d => add_smul c d (b j) })

end KIP126.Foundation
