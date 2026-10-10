import KIP126.Mathlib.SpectralSequence.FilteredComplex.Relations.Proofs

/-! Regression check for the canonical filtered-complex page view. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

noncomputable section

open CategoryTheory
open KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FilteredComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

example (FC : FilteredComplex C) :
  PageView FC :=
  PageView.canonical FC

example (FC : FilteredComplex C) (P : PageView FC)
    {r : ℤ} {hr : P.firstPage ≤ r} {s k : ℤ} {T : C}
    {x : P.element r hr s k T}
    {xl₁ xl₂ : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    (h₁ : P.IsLift r hr s k xl₁ x)
    (h₂ : P.IsLift r hr s k xl₂ x) :
    (FC.boundarySubobject s k (P.pageNumber r hr)).Factors
      ((xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k) :=
  P.isLift_sub_factors_boundary h₁ h₂

example (FC : FilteredComplex C) (P : PageView FC)
    {r : ℤ} {hr : P.firstPage ≤ r} {s k : ℤ} {T : C}
    {x : P.element r hr s k T}
    {y₁ y₂ : P.element r hr (s + r) (k - 1) T}
    (h₁ : P.relation r hr s k x y₁)
    (h₂ : P.relation r hr s k x y₂) : y₁ = y₂ :=
  P.relation_target_unique h₁ h₂

end

end KIP126.Core.SpectralSequence.FilteredComplex
