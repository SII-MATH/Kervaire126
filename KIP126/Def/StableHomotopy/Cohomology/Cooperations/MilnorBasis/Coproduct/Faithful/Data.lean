import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Proofs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v

/-- The basis index of the total-degree part of a tensor square. The first
degree is retained, so distinct direct-sum summands are not identified. -/
abbrev MilnorPair (n : ℤ) := Σ i : ℤ, MilnorMonomial i × MilnorMonomial (n - i)

/-- Put the two exponent vectors in distinct slots of the existing model. -/
def milnorPairExponents {n : ℤ} (d : MilnorPair n) : (Fin 2 × ℕ) →₀ ℕ :=
  d.2.1.val.mapDomain (fun j => ((0 : Fin 2), j)) +
    d.2.2.val.mapDomain (fun j => ((1 : Fin 2), j))

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- The full basis derived from the already constructed linear coordinates,
not an additional existence input. -/
def cooperationMilnorBasis (n : ℤ) :
    Module.Basis (MilnorMonomial n) F2 (mod2HomologyF2 H R n H.HF2) :=
  Module.Basis.ofRepr (cooperationMilnorEquiv H R B n)

/-- Tensor the derived full bases and take the basis of their direct sum. -/
def cooperationTensorMilnorBasis (n : ℤ) :
    Module.Basis (MilnorPair n) F2
      (cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) :=
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  DFinsupp.basis fun i => (cooperationMilnorBasis H R B i).tensorProduct (R := F2) (S := F2)
    (cooperationMilnorBasis H R B (n - i))

end

end KIP126.StableHomotopy.Cohomology
