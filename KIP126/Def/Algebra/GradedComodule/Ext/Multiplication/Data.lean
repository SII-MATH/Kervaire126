import KIP126.Def.Algebra.GradedComodule.Ext.Data
import KIP126.Def.Algebra.GradedComodule.Shift.TensorLine.Data
import KIP126.Def.Algebra.GradedComodule.Shift.Structure.Proofs
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
Yoneda multiplication in the actual category of graded right comodules.
The second factor is internally shifted and transported by the canonical
degree-line isomorphisms, then composed with the first factor. Compatibility
with left-to-right cobar concatenation is a separate comparison obligation.
-/

namespace KIP126.Algebra.GradedComodule

open CategoryTheory GradedVectorSpace

universe u

variable {K : Type u} [Field K] {C : Comon (GrVect K)}

noncomputable section

/-- Shift an actual coefficient Ext class by `t`, using the specified exact
internal shift and the canonical source and target comodule isomorphisms. -/
def coefficientShift (η : Coaugmentation C) (t : ℤ) (s' : ℕ) (u : ℤ) :
    CoefficientExt η s' u →ₗ[K]
      Abelian.Ext (trivialAt K η (t + u)) (trivialAt K η t) s' :=
  let sourceIso := internalShiftTrivialIso K η t u
  let targetIso :
      (internalShift K C t).obj (trivialAt K η 0) ≅ trivialAt K η t :=
    internalShiftTrivialIso K η t 0 ≪≫ eqToIso (by rw [add_zero])
  (Abelian.Ext.postcompOfLinear (Abelian.Ext.mk₀ targetIso.hom) K
      (trivialAt K η (t + u)) (Nat.add_zero s')).comp
    ((Abelian.Ext.precompOfLinear (Abelian.Ext.mk₀ sourceIso.inv) K
        ((internalShift K C t).obj (trivialAt K η 0)) (Nat.zero_add s')).comp
      ((internalShift K C t).mapExtLinearMap K
        (trivialAt K η u) (trivialAt K η 0) s'))

/-- The bigraded Yoneda product. The actual Ext composition is
`coefficientShift η t s' u y` followed by `x`; its degree `s' + s` is
identified with `s + s'`. No cobar comparison chooses this operation. -/
def coefficientYoneda (η : Coaugmentation C) (s s' : ℕ) (t u : ℤ) :
    CoefficientExt η s t →ₗ[K] CoefficientExt η s' u →ₗ[K]
      CoefficientExt η (s + s') (t + u) :=
  (Abelian.Ext.bilinearCompOfLinear K
    (trivialAt K η (t + u)) (trivialAt K η t) (trivialAt K η 0)
    s' s (s + s') (Nat.add_comm s' s)).flip.compl₂
      (coefficientShift η t s' u)

end

end KIP126.Algebra.GradedComodule
