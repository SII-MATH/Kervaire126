import KIP126.Def.Synthetic.Bockstein.Hom.Data
import KIP126.Def.Synthetic.Bockstein.Maps.Proofs
import KIP126.Def.Synthetic.QuotientRestrictions.Proofs
import KIP126.Def.Synthetic.QuotientRestrictions.Functoriality.Proofs

/-! Evaluation and local compatibility for the actual homotopy maps.
Identity and composition of restrictions retain the required coherence
of the specified cofiber-map choice. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

theorem betaPostcompose_apply (A : Syn) (q : ℕ) (n w : ℤ)
    (x : BiHom n w (XModLambdaN A q)) :
    betaPostcompose A q n w x = x ≫ beta A q := rfl

theorem betaHom_apply (A : Syn) (q : ℕ) (n w : ℤ)
    (x : BiHom n w (XModLambdaN A q)) :
    betaHom A q n w x =
      biSuspensionHomEquiv n w (q : ℤ) (XModLambdaN A 1) (x ≫ beta A q) := rfl

theorem restrictionHom_apply (coh : BiShiftCoherence Syn) (A : Syn)
    (i j : ℕ) (hij : i ≤ j) (n w : ℤ) (x : BiHom n w (XModLambdaN A j)) :
    restrictionHom coh A i j hij n w x =
      x ≫ XModLambdaN.restriction coh A i j hij := rfl

theorem firstRestrictionHom_apply (coh : BiShiftCoherence Syn) (A : Syn)
    (q : ℕ) (hq : 1 ≤ q) (n w : ℤ) (x : BiHom n w (XModLambdaN A q)) :
    firstRestrictionHom coh A q hq n w x =
      x ≫ XModLambdaN.restriction coh A 1 q hq := rfl

theorem betaHom_inclHom (A : Syn) (q : ℕ) (n w : ℤ) (x : BiHom n w A) :
    betaHom A q n w (inclHom A q n w x) = 0 := by
  change biSuspensionHomEquiv n w (q : ℤ) (XModLambdaN A 1)
    ((x ≫ XModLambdaN.incl A q) ≫ beta A q) = 0
  rw [Category.assoc, incl_beta, comp_zero, map_zero]

theorem restrictionHom_inclHom (coh : BiShiftCoherence Syn) (A : Syn)
    (i j : ℕ) (hij : i ≤ j) (n w : ℤ) (x : BiHom n w A) :
    restrictionHom coh A i j hij n w (inclHom A j n w x) = inclHom A i n w x := by
  change (x ≫ XModLambdaN.incl A j) ≫ XModLambdaN.restriction coh A i j hij =
    x ≫ XModLambdaN.incl A i
  rw [Category.assoc, XModLambdaN.incl_restriction]

theorem restrictionHom_self (coh : BiShiftCoherence Syn)
    (cofib : FunctorialCofiberCoherence Syn) (A : Syn) (i : ℕ) (n w : ℤ) :
    restrictionHom coh A i i le_rfl n w = AddMonoidHom.id _ := by
  ext x
  change x ≫ XModLambdaN.restriction coh A i i le_rfl = x
  rw [XModLambdaN.restriction_self coh cofib, Category.comp_id]

theorem restrictionHom_comp (coh : BiShiftCoherence Syn)
    (cofib : FunctorialCofiberCoherence Syn) (A : Syn)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (n w : ℤ) :
    (restrictionHom coh A i j hij n w).comp (restrictionHom coh A j k hjk n w) =
      restrictionHom coh A i k (hij.trans hjk) n w := by
  ext x
  change (x ≫ XModLambdaN.restriction coh A j k hjk) ≫
    XModLambdaN.restriction coh A i j hij =
      x ≫ XModLambdaN.restriction coh A i k (hij.trans hjk)
  rw [Category.assoc, XModLambdaN.restriction_comp coh cofib]

end KIP126.Synthetic.Bockstein
