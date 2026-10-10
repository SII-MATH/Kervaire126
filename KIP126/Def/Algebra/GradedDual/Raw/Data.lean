import KIP126.Def.Algebra.GradedVectorSpace.Data
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
The same-degree dual of an integer-graded vector space and the actual
homogeneous convolution maps of a graded coalgebra. The two tensor slots
retain their order. The natural map from the tensor of duals to the dual of
the tensor is used only as a map, with no finite-dimensionality assumption.
-/

namespace KIP126.Algebra.GradedDual

open CategoryTheory MonoidalCategory GradedVectorSpace

universe u
variable {K : Type u} [Field K]

noncomputable section

/-- The ordinary linear dual in each unchanged integer degree. -/
def degreewiseDual (X : GrVect K) : GrVect K :=
  fun n => ModuleCat.of K (Module.Dual K (X n))

/-- Transpose a degree-preserving map, reversing its direction but not the
internal grading. -/
def degreewiseDualMap {X Y : GrVect K} (f : X ⟶ Y) :
    degreewiseDual Y ⟶ degreewiseDual X :=
  fun n => ModuleCat.ofHom (f n).hom.dualMap

/-- Projection from a Cauchy tensor to its specified homogeneous summand.
It is the transported identity on that summand and zero on all others. -/
def tensorProjection (X Y : GrVect K) (i j : ℤ) :
    (X ⊗ Y) (i + j) ⟶ X i ⊗ Y j := by
  classical
  exact GradedObject.Monoidal.tensorObjDesc (fun a b _ =>
    if h : a = i ∧ b = j then
      eqToHom (congrArg₂ (fun a b => X a ⊗ Y b) h.1 h.2)
    else 0)

/-- The ordered `(i,j)` component of the given coalgebra's comultiplication. -/
def comultiplicationComponent (C : Comon (GrVect K)) (i j : ℤ) :
    C.X (i + j) ⟶ C.X i ⊗ C.X j :=
  (ComonObj.comul (X := C.X)) (i + j) ≫ tensorProjection C.X C.X i j

/-- Convolution on one pair of degrees: evaluate the first functional on
the first coproduct slot and the second functional on the second slot. -/
def convolutionPairing (C : Comon (GrVect K)) (i j : ℤ) :
    degreewiseDual C.X i ⊗ degreewiseDual C.X j ⟶ degreewiseDual C.X (i + j) :=
  ModuleCat.ofHom ((comultiplicationComponent C i j).hom.dualMap.comp
    (TensorProduct.dualDistrib K (C.X i) (C.X j)))

/-- Assemble the prescribed homogeneous pairings by the Cauchy coproduct
universal map, retaining the explicit degree transport. -/
def convolutionMultiplication (C : Comon (GrVect K)) :
    degreewiseDual C.X ⊗ degreewiseDual C.X ⟶ degreewiseDual C.X :=
  fun _n => GradedObject.Monoidal.tensorObjDesc (fun i j h =>
    convolutionPairing C i j ≫ eqToHom (congrArg (degreewiseDual C.X) h))

/-- The actual degree-zero counit, transported to the scalar field. -/
def scalarCounit (C : Comon (GrVect K)) : C.X 0 ⟶ ModuleCat.of K K :=
  (ComonObj.counit (X := C.X)) 0 ≫ GradedObject.Monoidal.tensorUnit₀.hom

/-- The convolution unit is the transpose of the given counit. In degree
zero use the actual tensor-unit isomorphism and `K → K*`, `r ↦ r • id`;
all other degree components are zero. -/
def convolutionUnit (C : Comon (GrVect K)) :
    𝟙_ (GrVect K) ⟶ degreewiseDual C.X := by
  classical
  intro n
  by_cases h : n = 0
  · subst n
    exact GradedObject.Monoidal.tensorUnit₀.hom ≫
      ModuleCat.ofHom ((scalarCounit C).hom.dualMap.comp
        (LinearMap.toSpanSingleton K (Module.Dual K K) LinearMap.id))
  · exact 0

end
end KIP126.Algebra.GradedDual
