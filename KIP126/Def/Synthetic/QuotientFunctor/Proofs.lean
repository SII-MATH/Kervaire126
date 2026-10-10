import KIP126.Def.Synthetic.QuotientFunctor.Data
import KIP126.Def.Synthetic.QuotientRestrictions.Proofs

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

@[simp] theorem XModLambdaN.restrictionNatTrans_self
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn) (i : ℕ) :
    XModLambdaN.restrictionNatTrans coh cofib i i le_rfl =
      𝟙 (XModLambdaN.functor cofib i) := by
  ext X
  exact XModLambdaN.restriction_self coh cofib X i

theorem XModLambdaN.restrictionNatTrans_comp
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    XModLambdaN.restrictionNatTrans coh cofib j k hjk ≫
        XModLambdaN.restrictionNatTrans coh cofib i j hij =
      XModLambdaN.restrictionNatTrans coh cofib i k (hij.trans hjk) := by
  ext X
  exact XModLambdaN.restriction_comp coh cofib X i j k hij hjk

/-- The restrictions lie under the identity functor through the actual
quotient inclusions. -/
theorem XModLambdaN.inclNatTrans_restriction
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn)
    (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.inclNatTrans cofib j ≫ XModLambdaN.restrictionNatTrans coh cofib i j hij =
      XModLambdaN.inclNatTrans cofib i := by
  ext X
  exact XModLambdaN.incl_restriction coh X i j hij

end KIP126.Synthetic.Context
