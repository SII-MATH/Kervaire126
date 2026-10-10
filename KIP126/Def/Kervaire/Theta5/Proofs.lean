import KIP126.Def.Kervaire.Theta5.Predicates

/-!
# Project transport for the BJM/BX criterion

These are generic conditional transport lemmas, with ordinary mathematical
hypotheses. They do not import Main or classify their premises as literature
inputs. The normalized criterion itself still needs a paper-level derivation
and a binding to the actual synthetic/Adams objects. The transport step is: an explicit order and
filtration comparison identifies the `lambda eta` square of any order-two
choice with that of the source choice, and ordinary rewriting transports both
the finite and infinite BJM/BX equivalences.
-/

namespace KIP126.Kervaire

section ChoiceTransport

variable {Carrier : Type} [AddCommGroup Carrier]
variable (C : Theta5ChoiceContext (Carrier := Carrier))

/-- Equality of the inductive expression for any two admissible choices. -/
theorem theta5_choice_independence
    (order : Theta5OrderData C)
    (correctionVanishes : ∀ {θ ψ},
      C.highDifference (C.difference θ ψ) →
        C.lambdaEta (C.correction θ ψ) = 0)
    {θ ψ : Carrier}
    (hθ : C.isChoice θ) (hψ : C.isChoice ψ)
    (_hθOrder : IsOrderTwo θ)
    (_hψOrder : IsOrderTwo ψ) :
    C.lambdaEta (C.square θ) = C.lambdaEta (C.square ψ) := by
  have hHigh : C.highDifference (C.difference θ ψ) :=
    order.2 θ ψ hθ hψ
  have hCorrection : C.lambdaEta (C.correction θ ψ) = 0 :=
    correctionVanishes hHigh
  have hSquare : C.square θ = C.square ψ + C.correction θ ψ := by
    calc
      C.square θ = C.square (ψ + C.difference θ ψ) := by
        rw [C.difference_spec θ ψ]
      _ = C.square ψ + C.correction θ ψ := by
        rw [C.difference_spec θ ψ]
        exact C.square_difference θ ψ
  rw [hSquare, map_add, hCorrection, add_zero]

/-- The source criterion transported to every order-two choice. -/
theorem bjm_bx_criterion_any_choice
    (criterion : BJM_BXCriterion C)
    (order : Theta5OrderData C)
    (correctionVanishes : ∀ {θ ψ},
      C.highDifference (C.difference θ ψ) →
        C.lambdaEta (C.correction θ ψ) = 0)
    {θ : Carrier}
    (hθ : C.isChoice θ)
    (hθOrder : IsOrderTwo θ) :
    (∀ r : ℕ, 1 ≤ r →
      (C.h6Survives (r + 3) ↔
        C.finiteZero (r + 1) (C.lambdaEta (C.square θ)))) ∧
      (C.is_permanent (C.lambdaEta (C.square θ)) ↔
        C.untruncatedZero (C.lambdaEta (C.square θ))) := by
  have hSourceChoice : C.isChoice C.sourceChoice := C.sourceChoice_isChoice
  have hSourceOrder : IsOrderTwo C.sourceChoice := criterion.1
  have hEqual : C.lambdaEta (C.square θ) =
      C.lambdaEta (C.square C.sourceChoice) :=
    theta5_choice_independence C order correctionVanishes hθ hSourceChoice
      hθOrder hSourceOrder
  constructor
  · intro r hr
    simpa [Theta5ChoiceContext.sourceExpression, hEqual] using
      (criterion.2.1 r hr)
  · simpa [Theta5ChoiceContext.sourceExpression, hEqual] using
      criterion.2.2

/-- The same transport theorem with the source and target expressions exposed
as a single `Iff`, useful to callers that keep finite and infinite criteria in
one dependent record. -/
theorem bjm_bx_criterion_any_choice_iff
    (criterion : BJM_BXCriterion C)
    (order : Theta5OrderData C)
    (correctionVanishes : ∀ {θ ψ},
      C.highDifference (C.difference θ ψ) →
        C.lambdaEta (C.correction θ ψ) = 0)
    {θ : Carrier}
    (hθ : C.isChoice θ)
    (hθOrder : IsOrderTwo θ) :
    (∀ r : ℕ, 1 ≤ r →
      (C.h6Survives (r + 3) ↔
        C.finiteZero (r + 1) (C.lambdaEta (C.square θ)))) ∧
      (C.is_permanent (C.lambdaEta (C.square θ)) ↔
        C.untruncatedZero (C.lambdaEta (C.square θ))) :=
  bjm_bx_criterion_any_choice C criterion order correctionVanishes hθ hθOrder

end ChoiceTransport

end KIP126.Kervaire
