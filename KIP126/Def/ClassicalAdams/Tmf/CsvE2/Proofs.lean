import KIP126.Def.ClassicalAdams.Tmf.CsvE2.Data
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Ring

/-! Homogeneity obligations for the fixed coordinate expressions.
These elementary proofs are deferred in the statement-only milestone. -/
namespace KIP126.Classical.Adams.Tmf.CsvE2

/-- The actual quotient-ring unit has bidegree `(0,0)`. -/
theorem one_mem_homogeneousPart : (1 : E2) ∈ homogeneousPart 0 0 := by
  sorry

/-- Multiplication in the fixed polynomial quotient adds bidegrees.
This is a property of the displayed monomial spans, not an extra product. -/
theorem mul_mem_homogeneousPart {s t s' t' : ℕ} {x y : E2}
    (hx : x ∈ homogeneousPart s t) (hy : y ∈ homogeneousPart s' t') :
    x * y ∈ homogeneousPart (s + s') (t + t') := by
  sorry

theorem v2SixteenValue_mem : v2SixteenValue ∈ homogeneousPart 16 112 := by
  sorry

theorem betaFiveGValue_mem : betaFiveGValue ∈ homogeneousPart 19 114 := by
  sorry

private instance polyCharTwo : CharP Poly 2 :=
  CharP.of_ringHom_of_ne_zero
    (MvPolynomial.C : KIP126.Core.Algebra.F2 →+* Poly) 2 (by decide)

private theorem relation_mem (terms : List (List (Generator × ℕ)))
    (h : terms ∈ relationPowers) : relationPolynomial terms ∈ definingIdeal :=
  Ideal.subset_span ⟨terms, h, rfl⟩

/-- The archived relation g²=βγ, also BR21 Table 3.4 / Table 3.5. -/
theorem g_square_eq_beta_gamma : generator 9 ^ 2 = generator 7 * generator 10 := by
  have h := relation_mem [[(9, 2)], [(7, 1), (10, 1)]] (by decide)
  change projection (MvPolynomial.X 9 ^ 2) =
    projection (MvPolynomial.X 7 * MvPolynomial.X 10)
  apply Ideal.Quotient.eq.mpr
  simpa [relationPolynomial, polynomialOfPowers, CharTwo.sub_eq_add] using h

/-- The archived relation gγ=β³, also BR21 Table 3.4 / Table 3.5. -/
theorem g_gamma_eq_beta_cube : generator 9 * generator 10 = generator 7 ^ 3 := by
  have h := relation_mem [[(9, 1), (10, 1)], [(7, 3)]] (by decide)
  change projection (MvPolynomial.X 9 * MvPolynomial.X 10) =
    projection (MvPolynomial.X 7 ^ 3)
  apply Ideal.Quotient.eq.mpr
  simpa [relationPolynomial, polynomialOfPowers, CharTwo.sub_eq_add] using h

/-- An equality in the actual fixed quotient, not an equality of class names. -/
theorem g_cube_eq_beta_four : generator 9 ^ 3 = generator 7 ^ 4 := by
  calc
    generator 9 ^ 3 = generator 7 * (generator 9 * generator 10) := by
      rw [pow_succ, g_square_eq_beta_gamma]
      ring
    _ = generator 7 ^ 4 := by rw [g_gamma_eq_beta_cube]; ring

/-- Converts BR21's βg⁴ to the selected β⁵g using the exact quotient relations. -/
theorem betaGFourValue_eq_betaFiveGValue : betaGFourValue = betaFiveGValue := by
  unfold betaGFourValue betaFiveGValue
  calc
    generator 7 * generator 9 ^ 4 = generator 7 * (generator 9 ^ 3 * generator 9) := by ring
    _ = generator 7 ^ 5 * generator 9 := by rw [g_cube_eq_beta_four]; ring

/-- The BR21 target is in the same bidegree by the proved equality. -/
theorem betaGFourValue_mem : betaGFourValue ∈ homogeneousPart 19 114 := by
  rw [betaGFourValue_eq_betaFiveGValue]
  exact betaFiveGValue_mem

end KIP126.Classical.Adams.Tmf.CsvE2
