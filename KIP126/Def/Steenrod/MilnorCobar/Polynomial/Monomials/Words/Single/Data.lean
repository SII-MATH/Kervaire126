import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data

namespace KIP126.Steenrod.Milnor

/-- A single positive monomial is exactly a length-one normalized word. -/
def singleMilnorWordEquiv (t : ℤ) : PositiveMonomial t ≃ MilnorWord 1 t where
  toFun a := ⟨fun _ => a.val, by simpa [wordDegree] using a.property.1,
    fun _ => a.property.2⟩
  invFun d := ⟨d.val 0, by simpa [wordDegree] using d.property.1, d.property.2 0⟩
  left_inv a := rfl
  right_inv d := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl

end KIP126.Steenrod.Milnor
