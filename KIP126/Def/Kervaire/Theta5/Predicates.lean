import KIP126.Def.Kervaire.Theta5.Data

/-!
# Mathematical predicates for the `theta_5` choice prototype

These definitions assert no conclusions. A predicate living in Def is part of
the mathematical language M; this does not make a proof of it an external input.
Some predicates below describe paper-derived conditions. The abstract context
still needs binding to the actual synthetic objects and internal Adams sequence.
-/

namespace KIP126.Kervaire

section Statements

variable {Carrier : Type} [AddCommGroup Carrier]
variable (C : Theta5ChoiceContext (Carrier := Carrier))

/-- Order and choice-filtration conditions. In a synthetic model these require
project deductions from classical Xu/IWX inputs and comparison/torsion results;
they must not be catalogued wholesale as a prior literature theorem. -/
def Theta5OrderData : Prop :=
  (∀ θ, C.isChoice θ → IsOrderTwo θ) ∧
    (∀ θ ψ, C.isChoice θ → C.isChoice ψ →
      C.highDifference (C.difference θ ψ))

/-- Paper-normalized source criterion (historical name retained). Its finite
clause uses λη and exponent r+1. Burklund--Xu Proposition 7.19 instead uses η
and exponent r; LWX Remark 7.4 needs a no-λ-torsion argument to pass between them.
This predicate is not itself the original A(M) input. Generic choice transport
is proved conditionally in `Proofs.lean`; actual model binding remains pending. -/
def BJM_BXCriterion : Prop :=
  IsOrderTwo C.sourceChoice ∧
    (∀ r : ℕ, 1 ≤ r →
      (C.h6Survives (r + 3) ↔
        C.finiteZero (r + 1) C.sourceExpression)) ∧
    (C.is_permanent C.sourceExpression ↔ C.untruncatedZero C.sourceExpression)

/-- The located total-differential identity for the distinguished source choice. -/
def SourceTotalDifferentialIdentity : Prop :=
  C.deltaH6 = C.lambdaEta (C.square C.sourceChoice)

/-- The universal choice transport is a project theorem, not a literature input. -/
def TotalDifferentialIdentity : Prop :=
  ∀ θ, C.isChoice θ → IsOrderTwo θ →
    C.deltaH6 = C.lambdaEta (C.square θ)

/-- Mixed intermediate conditions: derived order/choice comparison together
with two torsion conditions. This bundle is not a raw C(M) output; individual
source inputs and their project deductions must be separated before use. -/
def Theta5OrderTorsionEvidence : Prop :=
  Theta5OrderData C ∧ C.noLambdaTorsion62 ∧ C.noLambdaTorsion125

/-- Browder's geometric criterion, parameterized by one fixed framed context.
The existential side is the dimension-indexed statement used by the endpoint
theorems; the Adams permanence predicate is supplied by the same fixed sphere
sequence. -/
def BrowderCriterionStatement
    {Manifold : Type}
    (dimension : Manifold → ℕ)
    (kervaireOne : Manifold → Prop)
    (permanent : ℕ → Prop) : Prop :=
  ∀ n : ℕ,
    ((∃ M, dimension M = n ∧ kervaireOne M) ↔
      ∃ j : ℕ, 1 ≤ j ∧ n = 2 ^ (j + 1) - 2 ∧ permanent j)

/-- The HHR nonexistence result, with the project's framed-manifold predicate
and dimension convention as explicit parameters. -/
def HHRNonexistenceStatement
    {Manifold : Type}
    (dimension : Manifold → ℕ)
    (kervaireOne : Manifold → Prop) : Prop :=
  ∀ j : ℕ, 7 ≤ j →
    ¬ ∃ M, dimension M = 2 ^ (j + 1) - 2 ∧ kervaireOne M

/-- The Barratt--Jones--Mahowald inductive input. -/
def BJMInductionStatement
    {Class : Type}
    (detected : ℕ → Class → Prop)
    (isOrderTwo : Class → Prop)
    (squareZero : Class → Prop) : Prop :=
  ∀ j : ℕ, ∀ θ : Class,
    detected j θ → isOrderTwo θ → squareZero θ →
      ∃ next : Class, detected (j + 1) next ∧ isOrderTwo next

end Statements

end KIP126.Kervaire
