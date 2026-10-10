import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Expressions.Data
import KIP126.Def.SpectralSequence.Computation.Predicates

namespace KIP126.Classical.Adams

/-- A typed CSV-labelled equation for the EXISTING sphere differential.
It does not coerce arbitrary E₂ elements to Eᵣ or assume target nonvanishing. -/
def ExpressionDifferential {s t u v : ℕ} (r : ℤ)
    (x : LinE2.Expression s t) (y : LinE2.Expression u v)
    (hx : t ≤ 261) (hy : v ≤ 261) : Prop :=
  Core.SpectralSequence.HasDifferential sphereAdamsData r (s, t) (u, v)
    (expressionOnSphere x hx) (expressionOnSphere y hy)

end KIP126.Classical.Adams
