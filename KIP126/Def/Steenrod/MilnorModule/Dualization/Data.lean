import KIP126.Def.Steenrod.MilnorModule.Dualization.Raw.Proofs

/-! The actual contravariant dualization functor. Its internal grading is
unchanged and its left action uses the fixed recursive antipode. It is not
declared an equivalence, nor used by itself to identify derived Ext. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory KIP126.Algebra

noncomputable section

/-- The same-degree dual, with left action `a · φ = φ · χ(a)`. -/
def dualLeftModule (M : SourceComodule) : LeftModule :=
  GradedModule.ofAction steenrod (GradedDual.degreewiseDual M.A)
    (dualLeftAction M) (dualLeftAction_unit M) (dualLeftAction_assoc M)

/-- Degreewise transpose of the same underlying comodule map. -/
def dualLeftMap {M N : SourceComodule} (f : M ⟶ N) :
    dualLeftModule N ⟶ dualLeftModule M where
  f := GradedDual.degreewiseDualMap f.f
  h := dualLeftAction_naturality f

/-- Actual dualization has an opposite source; it does not negate internal degrees. -/
def dualToLeftModule : SourceComoduleᵒᵖ ⥤ LeftModule where
  obj M := dualLeftModule M.unop
  map f := dualLeftMap f.unop
  map_id _ := by
    apply Monad.Algebra.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    rfl
  map_comp _ _ := by
    apply Monad.Algebra.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    rfl

end
end KIP126.Steenrod.Milnor.Module
