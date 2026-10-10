import KIP126.Def.Steenrod.MilnorCoalgebra.Raw.Data

/-!
The recursive polynomial Milnor antipode, in the existing coproduct order
`Δ ξ_n = ∑ i, ξ_(n-i)^(2^i) ⊗ ξ_i`. Here generator index `j` is `ξ_(j+1)`.
In characteristic two the right antipode equation recursively prescribes
`S₀ = 1` and `S_n = ξ_n + ∑ 0 < i < n, ξ_(n-i)^(2^i) S_i`.
The two convolution contractions below act on the original two slots;
neither redefines or interchanges the given coproduct.
-/

namespace KIP126.Steenrod.Milnor.Coalgebra.Antipode

open KIP126.Core.Algebra
open scoped BigOperators

noncomputable section

/-- The recursively prescribed image of `ξ_n`, including `ξ₀ = 1`. -/
def generatorImage : ℕ → TensorPower 1 :=
  Nat.strongRec fun n previous =>
    if n = 0 then 1 else
      xi 0 n + ∑ i : Fin n, if i.val = 0 then 0 else
        xi 0 (n - i.val) ^ (2 ^ i.val) * previous i.val i.isLt

/-- Extend the specified generator images to the actual polynomial algebra. -/
def polynomialMap : TensorPower 1 →ₐ[F2] TensorPower 1 :=
  MvPolynomial.aeval fun a => generatorImage (a.2 + 1)

/-- The scalar augmentation, viewed as a constant-valued polynomial map. -/
def polynomialAugmentation : TensorPower 1 →ₐ[F2] TensorPower 1 :=
  MvPolynomial.aeval fun _ => 0

/-- Multiply the unchanged left slot with the antipode of the right slot. -/
def rightConvolution : TensorPower 2 →ₐ[F2] TensorPower 1 :=
  MvPolynomial.aeval fun a =>
    if a.1 = 0 then xi 0 (a.2 + 1) else generatorImage (a.2 + 1)

/-- Multiply the antipode of the left slot with the unchanged right slot. -/
def leftConvolution : TensorPower 2 →ₐ[F2] TensorPower 1 :=
  MvPolynomial.aeval fun a =>
    if a.1 = 0 then generatorImage (a.2 + 1) else xi 0 (a.2 + 1)

/-- The image of a full homogeneous basis monomial, before restriction. -/
def monomialImage {n : ℤ} (m : MilnorMonomial n) : TensorPower 1 :=
  polynomialMap (monomialPolynomial m)

end
end KIP126.Steenrod.Milnor.Coalgebra.Antipode
