import KIP126.Def.Steenrod.MilnorCoalgebra.Raw.Data

namespace KIP126.Steenrod.Milnor.Coalgebra

/-- Every actual term of the Milnor coproduct has the original total
degree. The construction of the graded coproduct uses all these terms. -/
theorem splitMonomial_support_degree {n : ℤ} (m : MilnorMonomial n)
    (d : (Fin 2 × ℕ) →₀ ℕ) (hd : d ∈ (splitMonomial m).support) :
    (slotWeight (slotExponentsEquiv 2 d 0) : ℤ) +
      (slotWeight (slotExponentsEquiv 2 d 1) : ℤ) = n := by
  sorry

end KIP126.Steenrod.Milnor.Coalgebra
