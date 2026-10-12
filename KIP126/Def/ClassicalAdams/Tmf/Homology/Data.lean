module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Data

@[expose] public section

/-! The graded coefficient spaces of
`F₂[ξ̄₁^8, ξ̄₂^4, ξ̄₃^2, ξ̄₄, …]`, the polynomial algebra appearing
in the BMQ mod-two homology calculation. The integer grading and exponent
restrictions are explicit. Identification with the homology of an actual
tmf spectrum is a separate mathematical comparison. -/

namespace KIP126.Classical.Adams.Tmf.Homology

open KIP126.Core.Algebra KIP126.Steenrod.Milnor

/-- The exponent of the generator ξ̄_(j+1) has degree `2^(j+1)-1`.
The first three exponents are multiples of 8, 4, and 2, respectively. -/
abbrev Monomial (n : ℤ) :=
  {d : MilnorMonomial n // 8 ∣ d.val 0 ∧ 4 ∣ d.val 1 ∧ 2 ∣ d.val 2}

/-- Finite linear combinations of monomials in one integer degree. -/
abbrev Coefficients (n : ℤ) := Monomial n →₀ F2

end KIP126.Classical.Adams.Tmf.Homology
