import KIP126.Def.Steenrod.MilnorModule.Data
import KIP126.Def.Steenrod.MilnorCoalgebra.Antipode.Proofs

/-! Same-degree dualization of a right comodule first gives a right module.
The specified Milnor antipode converts this into the left action below.
Neither a new conjugation map nor a change of coproduct convention is chosen. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory MonoidalCategory KIP126.Core.Algebra KIP126.Algebra
open GradedVectorSpace

noncomputable section

/-- The transpose of the actual recursive Milnor antipode. -/
def conjugation : steenrod.X ⟶ steenrod.X :=
  GradedDual.degreewiseDualMap Coalgebra.Antipode.map

/-- The fixed right-comodule category, before any dualization. -/
abbrev SourceComodule := GradedComodule.RightComodule Coalgebra.dualSteenrod

/-- The ordered homogeneous coaction component `M_(i+j) → M_i ⊗ C_j`. -/
def coactionComponent (M : SourceComodule) (i j : ℤ) :
    M.A (i + j) ⟶ M.A i ⊗ Coalgebra.dualSteenrod.X j :=
  M.a (i + j) ≫ GradedDual.tensorProjection M.A Coalgebra.dualSteenrod.X i j

/-- The actual right action on the same-degree dual: `(φ · a)(m)` is
evaluation of `φ ⊗ a` on the specified right coaction of `m`. -/
def dualRightPairing (M : SourceComodule) (i j : ℤ) :
    GradedDual.degreewiseDual M.A i ⊗ steenrod.X j ⟶
      GradedDual.degreewiseDual M.A (i + j) :=
  ModuleCat.ofHom ((coactionComponent M i j).hom.dualMap.comp
    (TensorProduct.dualDistrib F2 (M.A i) (Coalgebra.dualSteenrod.X j)))

/-- The left action is `a · φ = φ · χ(a)`, with the degree transport written
explicitly after braiding the input pair. -/
def dualLeftPairing (M : SourceComodule) (i j : ℤ) :
    steenrod.X i ⊗ GradedDual.degreewiseDual M.A j ⟶
      GradedDual.degreewiseDual M.A (i + j) :=
  (β_ (steenrod.X i) (GradedDual.degreewiseDual M.A j)).hom ≫
    (GradedDual.degreewiseDual M.A j ◁ conjugation i) ≫
      dualRightPairing M j i ≫
        eqToHom (congrArg (GradedDual.degreewiseDual M.A) (add_comm j i))

/-- Assemble the actual homogeneous left action with the Cauchy tensor's
universal map. No finite-dimensionality or dual-tensor inverse is used. -/
def dualLeftAction (M : SourceComodule) :
    steenrod.X ⊗ GradedDual.degreewiseDual M.A ⟶ GradedDual.degreewiseDual M.A :=
  fun _n => GradedObject.Monoidal.tensorObjDesc (fun i j h =>
    dualLeftPairing M i j ≫ eqToHom (congrArg (GradedDual.degreewiseDual M.A) h))

end
end KIP126.Steenrod.Milnor.Module
