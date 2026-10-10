import KIP126.Def.Steenrod.MilnorCoalgebra.Antipode.Raw.Data

/-! Properties of the fixed recursive polynomial maps. These are explicit
proof obligations, not additional choices of an antipode or its inverse. -/

namespace KIP126.Steenrod.Milnor.Coalgebra.Antipode

open KIP126.Core.Algebra
open scoped BigOperators

theorem generatorImage_zero : generatorImage 0 = 1 := by
  sorry

theorem generatorImage_rec (n : ℕ) (hn : 0 < n) :
    generatorImage n = xi 0 n + ∑ i : Fin n, if i.val = 0 then 0 else
      xi 0 (n - i.val) ^ (2 ^ i.val) * generatorImage i.val := by
  sorry

theorem polynomialMap_xi (n : ℕ) : polynomialMap (xi 0 n) = generatorImage n := by
  sorry

/-- Every supported term retains the original integer internal degree. -/
theorem monomialImage_support_degree {n : ℤ} (m : MilnorMonomial n)
    (d : (Fin 1 × ℕ) →₀ ℕ) (hd : d ∈ (monomialImage m).support) :
    (slotWeight (slotExponentsEquiv 1 d 0) : ℤ) = n := by
  sorry

/-- The recursive formula solves `m (id ⊗ S) Δ = η ε` for the original Δ. -/
theorem rightConvolution_split (p : TensorPower 1) :
    rightConvolution (splitSlot (s := 1) 0 p) = polynomialAugmentation p := by
  sorry

/-- The same specified map also satisfies the left antipode equation. -/
theorem leftConvolution_split (p : TensorPower 1) :
    leftConvolution (splitSlot (s := 1) 0 p) = polynomialAugmentation p := by
  sorry

/-- Milnor conjugation is involutive for this commutative polynomial algebra. -/
theorem polynomialMap_involutive (p : TensorPower 1) :
    polynomialMap (polynomialMap p) = p := by
  sorry

end KIP126.Steenrod.Milnor.Coalgebra.Antipode
