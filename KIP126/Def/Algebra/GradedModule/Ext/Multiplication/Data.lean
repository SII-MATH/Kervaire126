import KIP126.Def.Algebra.GradedModule.Ext.Data
import KIP126.Def.Algebra.GradedModule.Shift.TensorLine.Data
import KIP126.Def.Algebra.GradedModule.Shift.Structure.Proofs
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Yoneda multiplication for actual graded left-module Ext

The second factor is mapped by the specified exact internal shift and its
coefficient isomorphisms, then composed after the first factor in the actual
derived category.  No cobar or right-comodule comparison defines this product.
-/

namespace KIP126.Algebra.GradedModule

open CategoryTheory GradedVectorSpace

universe u

variable {K : Type u} [Field K] {A : Mon (GrVect K)}

noncomputable section

/-- Shift an actual left-module coefficient class by `t`, with the source and
target transported by the specified trivial-module isomorphisms. -/
def coefficientShift (ε : Augmentation A) (t : ℤ) (s' : ℕ) (u : ℤ) :
    CoefficientExt ε s' u →ₗ[K]
      Abelian.Ext (trivialAt K ε t) (trivialAt K ε (t + u)) s' :=
  let sourceIso :
      (internalShift K A t).obj (trivialAt K ε 0) ≅ trivialAt K ε t :=
    internalShiftTrivialIso K ε t 0 ≪≫ eqToIso (by rw [add_zero])
  let targetIso := internalShiftTrivialIso K ε t u
  (Abelian.Ext.postcompOfLinear (Abelian.Ext.mk₀ targetIso.hom) K
      (trivialAt K ε t) (Nat.add_zero s')).comp
    ((Abelian.Ext.precompOfLinear (Abelian.Ext.mk₀ sourceIso.inv) K
        ((internalShift K A t).obj (trivialAt K ε u)) (Nat.zero_add s')).comp
      ((internalShift K A t).mapExtLinearMap K
        (trivialAt K ε 0) (trivialAt K ε u) s'))

/-- The left-module Yoneda product is `x` followed by the internally shifted
`y`.  Its actual Ext composition has degree `s+s'`; the named factors are
kept in their original order. -/
def coefficientYoneda (ε : Augmentation A) (s s' : ℕ) (t u : ℤ) :
    CoefficientExt ε s t →ₗ[K] CoefficientExt ε s' u →ₗ[K]
      CoefficientExt ε (s + s') (t + u) :=
  (Abelian.Ext.bilinearCompOfLinear K
    (trivialAt K ε 0) (trivialAt K ε t) (trivialAt K ε (t + u))
    s s' (s + s') rfl).compl₂ (coefficientShift ε t s' u)

end

end KIP126.Algebra.GradedModule
