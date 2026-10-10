import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Faithful.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v

theorem milnorPairExponents_zero {n : ℤ} (d : MilnorPair n) (j : ℕ) :
    milnorPairExponents d (0, j) = d.2.1.val j := by
  have hi : Function.Injective (fun j : ℕ => ((0 : Fin 2), j)) := fun _ _ h =>
    congrArg Prod.snd h
  have hn : (0, j) ∉ Set.range (fun k : ℕ => ((1 : Fin 2), k)) := by simp
  simp only [milnorPairExponents, Finsupp.add_apply, Finsupp.mapDomain_apply hi,
    Finsupp.mapDomain_notin_range _ _ hn, add_zero]

theorem milnorPairExponents_one {n : ℤ} (d : MilnorPair n) (j : ℕ) :
    milnorPairExponents d (1, j) = d.2.2.val j := by
  have hi : Function.Injective (fun j : ℕ => ((1 : Fin 2), j)) := fun _ _ h =>
    congrArg Prod.snd h
  have hn : (1, j) ∉ Set.range (fun k : ℕ => ((0 : Fin 2), k)) := by simp
  simp only [milnorPairExponents, Finsupp.add_apply, Finsupp.mapDomain_apply hi,
    Finsupp.mapDomain_notin_range _ _ hn, zero_add]

/-- The first exponent vector also recovers its summand degree by weight. -/
theorem milnorPairExponents_injective (n : ℤ) :
    Function.Injective (milnorPairExponents (n := n)) := by
  rintro ⟨i, a, b⟩ ⟨i', a', b'⟩ h
  have ha : a.val = a'.val := by
    ext j
    have hh := congrArg (fun d => d (0, j)) h
    simpa only [milnorPairExponents_zero] using hh
  have hi : i = i' := a.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) ha).trans a'.property)
  subst i'
  have haa : a = a' := Subtype.ext ha
  have hb : b = b' := by
    apply Subtype.ext
    ext j
    have hh := congrArg (fun d => d (1, j)) h
    simpa only [milnorPairExponents_one] using hh
  cases haa
  cases hb
  rfl

/-- Concatenating two basis monomials gives their two-slot exponent vector. -/
theorem cup_milnorMonomialPolynomial {n : ℤ} (d : MilnorPair n) :
    cupPolynomial (milnorMonomialPolynomial d.2.1) (milnorMonomialPolynomial d.2.2) =
      MvPolynomial.monomial (milnorPairExponents d) (1 : F2) := by
  simp only [cupPolynomial, milnorMonomialPolynomial, MvPolynomial.rename_monomial,
    ← Finsupp.mapDomain_comp, MvPolynomial.monomial_mul, mul_one]
  rfl

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

theorem cooperationMilnorPolynomial_basis (n : ℤ) (d : MilnorMonomial n) :
    cooperationMilnorPolynomial H R B n (cooperationMilnorBasis H R B n d) =
      milnorMonomialPolynomial d := by
  simp [cooperationMilnorBasis, Module.Basis.coe_ofRepr, cooperationMilnorPolynomial,
    Finsupp.linearCombination_single]

/-- Single-slot polynomial coordinates lose no cooperation classes. -/
theorem cooperationMilnorPolynomial_injective (n : ℤ) :
    Function.Injective (cooperationMilnorPolynomial H R B n) := by
  have hi : Function.Injective (fun d : MilnorMonomial n =>
      d.val.mapDomain fun j => ((0 : Fin 1), j)) := by
    intro d e h
    apply Subtype.ext
    exact Finsupp.mapDomain_injective (fun _ _ h => congrArg Prod.snd h) h
  have hl := (MvPolynomial.basisMonomials (Fin 1 × ℕ) F2).linearIndependent.comp _ hi
  have hl' : LinearIndependent F2 (milnorMonomialPolynomial (n := n)) := hl
  exact hl'.finsuppLinearCombination_injective.comp (cooperationMilnorEquiv H R B n).injective

theorem cooperationTensorMilnorBasis_apply (n : ℤ) (d : MilnorPair n) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    cooperationTensorMilnorBasis H R B n d = DirectSum.lof F2 ℤ _ d.1
      (cooperationMilnorBasis H R B d.1 d.2.1 ⊗ₜ[F2]
        cooperationMilnorBasis H R B (n - d.1) d.2.2) := by
  change (cooperationTensorMilnorBasis H R B n).repr.symm (Finsupp.single d 1) = _
  dsimp only [cooperationTensorMilnorBasis, DFinsupp.basis]
  erw [LinearEquiv.symm_trans_apply]
  simp only [LinearEquiv.symm_symm]
  erw [DFinsupp.mapRange.linearEquiv_symm]
  simp only [sigmaFinsuppLequivDFinsupp]
  erw [DFinsupp.mapRange.linearEquiv_apply]
  erw [sigmaFinsuppEquivDFinsupp_single]
  erw [DFinsupp.mapRange_single, Module.Basis.repr_symm_single_one,
    Module.Basis.tensorProduct_apply']
  rfl

theorem cooperationTensorMilnorPolynomial_basis (n : ℤ) (d : MilnorPair n) :
    cooperationTensorMilnorPolynomial H R B n (cooperationTensorMilnorBasis H R B n d) =
      MvPolynomial.monomial (milnorPairExponents d) (1 : F2) := by
  rw [cooperationTensorMilnorBasis_apply]
  erw [cooperationTensorMilnorPolynomial_lof_tmul]
  rw [cooperationMilnorPolynomial_basis, cooperationMilnorPolynomial_basis,
    cup_milnorMonomialPolynomial]

/-- The tensor polynomial map is faithful across all total-degree summands,
not only within a chosen pair of factors. -/
theorem cooperationTensorMilnorPolynomial_injective (n : ℤ) :
    Function.Injective (cooperationTensorMilnorPolynomial H R B n) := by
  apply LinearMap.injective_of_linearIndependent (cooperationTensorMilnorBasis H R B n).span_eq
  have hl := (MvPolynomial.basisMonomials (Fin 2 × ℕ) F2).linearIndependent.comp _
    (milnorPairExponents_injective n)
  simpa only [Function.comp_def, cooperationTensorMilnorPolynomial_basis,
    MvPolynomial.coe_basisMonomials] using hl

/-- A proposed value of the actual coproduct can be checked by a polynomial
identity. Faithfulness makes this an equivalence, not just a forward test. -/
theorem cooperationTensorDiagonal_eq_iff (K : Mod2CooperationKunneth H R)
    (hU : Mod2KunnethUnitCompatible H R K) (hM : Mod2MilnorCoproductCompatible H R K B)
    (n : ℤ) (a : Mod2Cooperations H n)
    (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) :
    cooperationTensorDiagonal H R K n a = z ↔
      splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a) =
        cooperationTensorMilnorPolynomial H R B n z := by
  rw [← (cooperationTensorMilnorPolynomial_injective H R B n).eq_iff,
    cooperationMilnorCoproduct H R B K hU hM]

end

end KIP126.StableHomotopy.Cohomology
