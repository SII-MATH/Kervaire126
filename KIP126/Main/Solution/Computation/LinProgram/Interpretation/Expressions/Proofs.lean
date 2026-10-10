import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Expressions.Data
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Proofs

set_option maxRecDepth 16384

namespace KIP126.Classical.Adams
open KIP126.LinE2
attribute [local irreducible] homogeneousPart generatorDegree definingIdeal

theorem expressionOnSphere_zero (s t : ℕ) (ht : t ≤ 261) :
    expressionOnSphere (.zero s t) ht = 0 := by
  exact (linToSphereE2 s t ht).map_zero

theorem expressionOnSphere_add {s t : ℕ} (a b : Expression s t) (ht : t ≤ 261) :
    expressionOnSphere (.add a b) ht = expressionOnSphere a ht + expressionOnSphere b ht := by
  exact (linToSphereE2 s t ht).map_add a.value b.value

/-- Uses #119's existing E₂ product and its explicit comparison assumption. -/
theorem expressionOnSphere_mul {s t s' t' : ℕ}
    (a : Expression s t) (b : Expression s' t') (ht : t + t' ≤ 261) :
    expressionOnSphere (.mul a b) ht =
      linE2Presentation.product s t s' t'
        (expressionOnSphere a (by omega)) (expressionOnSphere b (by omega)) :=
  linToSphere_mul ht a.value b.value

/-- The migrated generator is the already chosen computedH6, not a new class. -/
theorem expressionOnSphere_h6 :
    expressionOnSphere h6Expression (by decide) = computedH6 := by
  have h : h6Expression.value = dataH6 :=
    Subtype.ext (Expression.data_cast h6Generator_degree (.gen h6Generator))
  exact congrArg (linToSphereE2 1 64 (by decide)) h

/-- The expression square and the existing final-goal class coincide. -/
theorem expressionOnSphere_h6_square :
    expressionOnSphere h6SqExpression (by decide) = computedH6Square := by
  change expressionOnSphere (.mul h6Expression h6Expression) _ = computedH6Square
  rw [expressionOnSphere_mul, expressionOnSphere_h6, computedH6_mul_self]

end KIP126.Classical.Adams
