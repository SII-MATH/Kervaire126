module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.Orthogonality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- Scalar-complete objects are closed under the middle object of an
actual distinguished triangle. -/
theorem SourceIsScalarComplete.triangle_middle (p : ℕ) (T : Triangle SourceCategory.{u})
    (hT : T ∈ distTriang SourceCategory) (h₁ : SourceIsScalarComplete p T.obj₁)
    (h₃ : SourceIsScalarComplete p T.obj₃) : SourceIsScalarComplete p T.obj₂ := by
  intro U hU
  letI := h₁ U hU
  letI := h₃ U hU
  have hz (a : U ⟶ T.obj₂) : a = 0 := by
    obtain ⟨b,hb⟩ := T.coyoneda_exact₂ hT a (Subsingleton.elim _ _)
    rw [show b = 0 from Subsingleton.elim _ _] at hb
    exact hb.trans Limits.zero_comp
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Scalar-complete objects are closed under the third object of an
actual distinguished triangle. -/
theorem SourceIsScalarComplete.triangle_third (p : ℕ) (T : Triangle SourceCategory.{u})
    (hT : T ∈ distTriang SourceCategory) (h₁ : SourceIsScalarComplete p T.obj₁)
    (h₂ : SourceIsScalarComplete p T.obj₂) : SourceIsScalarComplete p T.obj₃ :=
  SourceIsScalarComplete.triangle_middle p T.rotate (rot_of_distTriang _ hT)
    h₂ (h₁.shift 1)

/-- Scalar-complete objects are closed under the first object of an
actual distinguished triangle. -/
theorem SourceIsScalarComplete.triangle_first (p : ℕ) (T : Triangle SourceCategory.{u})
    (hT : T ∈ distTriang SourceCategory) (h₂ : SourceIsScalarComplete p T.obj₂)
    (h₃ : SourceIsScalarComplete p T.obj₃) : SourceIsScalarComplete p T.obj₁ := by
  apply SourceIsScalarComplete.triangle_middle p T.invRotate (inv_rot_of_distTriang _ hT) _ h₂
  change SourceIsScalarComplete p (T.obj₃⟦(-1 : ℤ)⟧)
  exact h₃.shift (-1)

end KIP126.StableHomotopy.Implementation
