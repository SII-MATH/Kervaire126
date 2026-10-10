import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Leibniz.Predicates

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : AdamsLongLayerPairing unit X r hr p q)
  (hP : P.ProjectionCompatible) (hB : P.BoundaryCompatible)
  (L : adamsPage unit X r hr (p.1 + r) (p.2 + r - 1) →ₗ[ℤ]
    adamsPage unit X r hr q.1 q.2 →ₗ[ℤ]
      adamsPage unit X r hr ((p.1 + q.1) + r) ((p.2 + q.2) + r - 1))
  (R : adamsPage unit X r hr p.1 p.2 →ₗ[ℤ]
    adamsPage unit X r hr (q.1 + r) (q.2 + r - 1) →ₗ[ℤ]
      adamsPage unit X r hr ((p.1 + q.1) + r) ((p.2 + q.2) + r - 1))
  (e : ℤ)

/-- The relative boundary identity suffices for the Leibniz formula for the
actual tower differential and the constructed quotient pairing. This does not
claim the geometric identity, the correct sign, or the Lin comparison. -/
theorem AdamsLongLayerPairing.leibniz_of_relativeBoundary
    (h : P.RelativeBoundaryFormula L R e)
    (x : adamsPage unit X r hr p.1 p.2) (y : adamsPage unit X r hr q.1 q.2) :
    adamsDifferential unit X r hr (p.1 + q.1) (p.2 + q.2) (P.onPage hP hB x y) =
      L (adamsDifferential unit X r hr p.1 p.2 x) y +
        e • R x (adamsDifferential unit X r hr q.1 q.2 y) := by
  obtain ⟨a, rfl⟩ := adamsLongLayerToPage_surjective unit X r hr p.1 p.2 x
  obtain ⟨b, rfl⟩ := adamsLongLayerToPage_surjective unit X r hr q.1 q.2 y
  rw [P.onPage_long hP hB]
  simp only [adamsDifferential_longLayerToPage_eq_boundary]
  exact h a b

/-- Conversely the page formula evaluated on long representatives recovers
the relative boundary identity. Thus this is an exact remaining obligation,
not a hidden proof of multiplicativity or an unnecessarily strong global
morphism equality. -/
theorem AdamsLongLayerPairing.relativeBoundary_iff_leibniz :
    P.RelativeBoundaryFormula L R e ↔
      ∀ x y, adamsDifferential unit X r hr (p.1 + q.1) (p.2 + q.2) (P.onPage hP hB x y) =
        L (adamsDifferential unit X r hr p.1 p.2 x) y +
          e • R x (adamsDifferential unit X r hr q.1 q.2 y) := by
  constructor
  · exact P.leibniz_of_relativeBoundary hP hB L R e
  · intro h a b
    have hab := h (adamsLongLayerToPage unit X r hr p.1 p.2 a)
      (adamsLongLayerToPage unit X r hr q.1 q.2 b)
    rw [P.onPage_long hP hB] at hab
    simpa only [adamsDifferential_longLayerToPage_eq_boundary] using hab

end
end KIP126.Classical.Adams
