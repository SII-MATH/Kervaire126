import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Faithful.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Right.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

theorem cooperationMilnorPolynomial_cast (i j : ℤ) (h : i = j)
    (a : Mod2Cooperations H i) :
    cooperationMilnorPolynomial H R B j
      ((LinearEquiv.cast (R := F2) (M := fun k => mod2HomologyF2 H R k H.HF2) h) a) =
      cooperationMilnorPolynomial H R B i a := by
  subst j
  rfl

theorem cooperationTensorMilnorPolynomial_leftUnit (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorMilnorPolynomial H R B n
      (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a) =
      insertLeft 1 (cooperationMilnorPolynomial H R B n a) := by
  rw [cooperationTensorUnit_apply, cooperationTensorMilnorPolynomial_lof_tmul,
    cooperationMilnorPolynomial_cast, cooperationMilnorPolynomial_unit]
  simp [cupPolynomial, insertLeft]

theorem cooperationTensorMilnorPolynomial_rightUnit (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorMilnorPolynomial H R B n (cooperationTensorRightUnit H R n a) =
      insertRight 1 (cooperationMilnorPolynomial H R B n a) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  change cooperationTensorMilnorPolynomial H R B n
    (DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
      (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
        (sub_self n).symm) (cooperationUnit H))) = _
  rw [cooperationTensorMilnorPolynomial_lof_tmul, cooperationMilnorPolynomial_cast,
    cooperationMilnorPolynomial_unit]
  simp only [cupPolynomial, map_one, mul_one]
  rfl

/-- The concrete polynomial used for h₆ has a unique actual cooperation
representative, constructed from the derived full basis. -/
theorem cooperationMilnorPolynomial_h6_existsUnique :
    ∃! a : Mod2Cooperations H 64,
      cooperationMilnorPolynomial H R B 64 a = h6Polynomial := by
  let d : MilnorMonomial 64 := ⟨Finsupp.single 0 64, by simp [slotWeight, Finsupp.weight_single]⟩
  have hd : cooperationMilnorPolynomial H R B 64 (cooperationMilnorBasis H R B 64 d) =
      h6Polynomial := by
    rw [cooperationMilnorPolynomial_basis]
    simp [milnorMonomialPolynomial, d, h6Polynomial, MvPolynomial.X_pow_eq_monomial]
  refine ⟨cooperationMilnorBasis H R B 64 d, hd, ?_⟩
  intro a ha
  exact cooperationMilnorPolynomial_injective H R B 64 (ha.trans hd.symm)

variable (K : Mod2CooperationKunneth H R)

/-- A cooperation with the specified nonzero polynomial cannot vanish. -/
theorem cooperation_ne_zero_of_h6Polynomial (a : Mod2Cooperations H 64)
    (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) : a ≠ 0 := by
  have hp : h6Polynomial ≠ (0 : TensorPower 1) := by
    simp [h6Polynomial, MvPolynomial.X_pow_eq_monomial]
  intro hz
  apply hp
  rw [← ha, hz]
  exact (cooperationMilnorPolynomial H R B 64).map_zero

/-- Primitivity in actual cooperation tensors is exactly the polynomial
formula, not merely a necessary condition in a quotient of the tensors. -/
theorem cooperationTensorDiagonal_primitive_iff
    (hU : Mod2KunnethUnitCompatible H R K) (hM : Mod2MilnorCoproductCompatible H R K B)
    (n : ℤ) (a : Mod2Cooperations H n) :
    cooperationTensorDiagonal H R K n a =
        cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a +
          cooperationTensorRightUnit H R n a ↔
      splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a) =
        insertLeft 1 (cooperationMilnorPolynomial H R B n a) +
          insertRight 1 (cooperationMilnorPolynomial H R B n a) := by
  rw [← (cooperationTensorMilnorPolynomial_injective H R B n).eq_iff,
    cooperationMilnorCoproduct H R B K hU hM, map_add,
    cooperationTensorMilnorPolynomial_leftUnit, cooperationTensorMilnorPolynomial_rightUnit]

/-- The concrete primitive power used in the standard h₆ cocycle has an
actual primitive cooperation representative whenever the low-level Milnor
comparison holds. This is not a statement of higher-page permanence. -/
theorem cooperationTensorDiagonal_primitive_of_h6Polynomial
    (hU : Mod2KunnethUnitCompatible H R K) (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial) :
    cooperationTensorDiagonal H R K 64 a =
      cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 64 a +
        cooperationTensorRightUnit H R 64 a := by
  apply (cooperationTensorDiagonal_primitive_iff H R B K hU hM 64 a).mpr
  rw [ha]
  have hp (x y : TensorPower 2) : (x + y) ^ 64 = x ^ 64 + y ^ 64 :=
    add_pow_char_pow x y 2 6
  simp [h6Polynomial, splitSlot, coproductGenerator, xi, Finset.sum_range_succ,
    insertLeft, insertRight, hp, add_comm]

/-- The primitive h₆ polynomial is realized uniquely in genuine cooperation
groups under the low-level comparisons; no new element-existence input is used. -/
theorem cooperationTensorDiagonal_h6_existsUnique
    (hU : Mod2KunnethUnitCompatible H R K) (hM : Mod2MilnorCoproductCompatible H R K B) :
    ∃! a : Mod2Cooperations H 64,
      cooperationMilnorPolynomial H R B 64 a = h6Polynomial ∧
        cooperationTensorDiagonal H R K 64 a =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 64 a +
            cooperationTensorRightUnit H R 64 a := by
  obtain ⟨a, ha, hu⟩ := cooperationMilnorPolynomial_h6_existsUnique H R B
  exact ⟨a, ⟨ha, cooperationTensorDiagonal_primitive_of_h6Polynomial H R B K hU hM a ha⟩,
    fun b hb => hu b hb.1⟩

end

end KIP126.StableHomotopy.Cohomology
