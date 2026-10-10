import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.Data

namespace KIP126.Classical.Adams

/-- The actual tower d₂, expressed through this Lin comparison, obeys the
characteristic-two Leibniz rule. Equality is in the common ambient quotient
to avoid associativity casts between homogeneous components. All differential
targets, including that of the product, must lie in the covered range.
This is a missing compatibility property, not a consequence of the E₂ table. -/
def LinE2Presentation.SecondDifferentialLeibniz (P : LinE2Presentation) : Prop :=
  ∀ (s t s' t' : ℕ) (h : t + t' + 1 ≤ 261)
    (x : KIP126.LinE2.E2At s t) (y : KIP126.LinE2.E2At s' t'),
    (P.secondDifferential (s + s') (t + t') h (KIP126.LinE2.mulAt x y)).val =
      (P.secondDifferential s t (by omega) x).val * y.val +
        x.val * (P.secondDifferential s' t' (by omega) y).val

end KIP126.Classical.Adams
