import KIP126.LinProgram.Interpretation.Expression.Value.Data
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

namespace KIP126.Classical.Adams

/-- The migrated expression interpreter lands on #119's fixed, tower-derived
sphere Adams E₂ via its existing comparison. No historical transfer is used. -/
noncomputable def expressionOnSphere {s t : ℕ} (e : LinE2.Expression s t)
    (ht : t ≤ 261) : sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) :=
  linToSphereE2 s t ht e.value

end KIP126.Classical.Adams
