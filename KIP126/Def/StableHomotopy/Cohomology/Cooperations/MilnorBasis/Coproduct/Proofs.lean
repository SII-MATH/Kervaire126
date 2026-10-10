import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

theorem milnorMonomialPolynomial_zero :
    milnorMonomialPolynomial zeroMilnorMonomial = 1 := by
  simp [milnorMonomialPolynomial, zeroMilnorMonomial]

theorem cooperationMilnorPolynomial_unit :
    cooperationMilnorPolynomial H R B 0 (cooperationUnit H) = 1 := by
  simp [cooperationMilnorPolynomial, cooperationMilnorEquiv_unit,
    Finsupp.linearCombination_single, milnorMonomialPolynomial_zero]

theorem cooperationMilnorPolynomial_reduced_basis (n : ℤ) (d : PositiveMonomial n) :
    cooperationMilnorPolynomial H R B n ((B.basis n) d).val =
      milnorMonomialPolynomial (⟨d.val, d.property.1⟩ : MilnorMonomial n) := by
  simp [cooperationMilnorPolynomial, cooperationMilnorEquiv_reduced_basis,
    Finsupp.linearCombination_single]

theorem cooperationTensorMilnorPolynomial_lof_tmul (n i : ℤ)
    (a : Mod2Cooperations H i) (b : Mod2Cooperations H (n - i)) :
    letI : ∀ j, Module F2 (Mod2Cooperations H j) :=
      fun j => mod2HomologyModule H R j H.HF2
    cooperationTensorMilnorPolynomial H R B n (DirectSum.lof F2 ℤ _ i (a ⊗ₜ[F2] b)) =
      cupPolynomial (cooperationMilnorPolynomial H R B i a)
        (cooperationMilnorPolynomial H R B (n - i) b) := by
  simp only [cooperationTensorMilnorPolynomial, DirectSum.toModule_lof,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    cupPolynomial, AlgHom.toLinearMap_apply]
  rfl

theorem cooperationTensorMilnorPolynomial_unit :
    cooperationTensorMilnorPolynomial H R B 0
      (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 0
        (cooperationUnit H)) = 1 := by
  rw [cooperationTensorUnit_apply, cooperationTensorMilnorPolynomial_lof_tmul]
  change cupPolynomial (cooperationMilnorPolynomial H R B 0 (cooperationUnit H))
    (cooperationMilnorPolynomial H R B 0 (cooperationUnit H)) = 1
  simp [cooperationMilnorPolynomial_unit, cupPolynomial]

variable (K : Mod2CooperationKunneth H R)

/-- The constant case of the Milnor coproduct formula follows from
unit coherence, rather than being included in the basis input. -/
theorem cooperationMilnorCoproduct_unit (hU : Mod2KunnethUnitCompatible H R K) :
    cooperationTensorMilnorPolynomial H R B 0
      (cooperationTensorDiagonal H R K 0 (cooperationUnit H)) =
      splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B 0 (cooperationUnit H)) := by
  rw [cooperationTensorDiagonal_unit H R K hU, cooperationTensorMilnorPolynomial_unit,
    cooperationMilnorPolynomial_unit, map_one]

/-- A basis-level coproduct comparison and unit coherence imply the formula
on every actual cooperation, by linearity. This does not assert either input. -/
theorem cooperationMilnorCoproduct (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B) (n : ℤ)
    (a : Mod2Cooperations H n) :
    cooperationTensorMilnorPolynomial H R B n (cooperationTensorDiagonal H R K n a) =
      splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a) := by
  let f := fun n => (cooperationTensorMilnorPolynomial H R B n).comp
    (cooperationTensorDiagonal H R K n)
  let g := fun n => (splitSlot (0 : Fin 1)).toLinearMap.comp
    (cooperationMilnorPolynomial H R B n)
  have he : f = g := cooperation_linearMap_ext H R B f g
    (cooperationMilnorCoproduct_unit H R B K hU) (by
      intro n d
      change cooperationTensorMilnorPolynomial H R B n
        (cooperationTensorDiagonal H R K n ((B.basis n) d).val) =
        splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n ((B.basis n) d).val)
      rw [cooperationMilnorPolynomial_reduced_basis]
      exact hM n d)
  exact LinearMap.congr_fun (congrFun he n) a

/-- The reduced-basis condition is exactly the full formula, once unit
coherence is supplied; it is not an assumption about Adams differentials. -/
theorem mod2MilnorCoproductCompatible_iff (hU : Mod2KunnethUnitCompatible H R K) :
    Mod2MilnorCoproductCompatible H R K B ↔
      ∀ n (a : Mod2Cooperations H n),
        cooperationTensorMilnorPolynomial H R B n (cooperationTensorDiagonal H R K n a) =
          splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a) := by
  constructor
  · exact cooperationMilnorCoproduct H R B K hU
  · intro h n d
    simpa only [cooperationMilnorPolynomial_reduced_basis] using h n ((B.basis n) d).val

end

end KIP126.StableHomotopy.Cohomology
