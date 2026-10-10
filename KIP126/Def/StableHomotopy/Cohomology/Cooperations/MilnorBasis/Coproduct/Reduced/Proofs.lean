import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Faithful.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- The full cooperation basis restricts to the supplied reduced basis,
with exactly the same underlying represented elements. -/
theorem cooperationMilnorBasis_reduced (n : ℤ) (a : PositiveMonomial n) :
    cooperationMilnorBasis H R B n ⟨a.val, a.property.1⟩ = (B.basis n a).val := by
  apply (cooperationMilnorEquiv H R B n).injective
  rw [cooperationMilnorEquiv_reduced_basis]
  simp [cooperationMilnorBasis, Module.Basis.coe_ofRepr]

/-- Every polynomial coefficient at a tensor-basis exponent is exactly
the corresponding actual tensor-basis coefficient. -/
theorem cooperationTensorMilnorPolynomial_coeff (n : ℤ)
    (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n)
    (d : MilnorPair n) :
    MvPolynomial.coeff (milnorPairExponents d) (cooperationTensorMilnorPolynomial H R B n z) =
      (cooperationTensorMilnorBasis H R B n).repr z d := by
  classical
  let f := (MvPolynomial.lcoeff F2 (milnorPairExponents d)).comp
    (cooperationTensorMilnorPolynomial H R B n)
  let g := (Finsupp.lapply (R := F2) d).comp
    (cooperationTensorMilnorBasis H R B n).repr.toLinearMap
  have hfg : f = g := by
    apply (cooperationTensorMilnorBasis H R B n).ext
    intro e
    change MvPolynomial.coeff (milnorPairExponents d)
      (cooperationTensorMilnorPolynomial H R B n (cooperationTensorMilnorBasis H R B n e)) =
      (cooperationTensorMilnorBasis H R B n).repr (cooperationTensorMilnorBasis H R B n e) d
    rw [cooperationTensorMilnorPolynomial_basis, Module.Basis.repr_self]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_apply,
      (milnorPairExponents_injective n).eq_iff]
  exact LinearMap.congr_fun hfg z

/-- Polynomial normalization forces both factors of every supported
actual tensor-basis term to be nonconstant. -/
theorem cooperationTensorMilnorBasis_support_reduced (n : ℤ)
    (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n)
    (hz : ∀ j : Fin 2, augmentSlot j (cooperationTensorMilnorPolynomial H R B n z) = 0)
    (d : MilnorPair n) (hd : (cooperationTensorMilnorBasis H R B n).repr z d ≠ 0) :
    d.2.1.val ≠ 0 ∧ d.2.2.val ≠ 0 := by
  have hc : MvPolynomial.coeff (milnorPairExponents d)
      (cooperationTensorMilnorPolynomial H R B n z) ≠ 0 := by
    rw [cooperationTensorMilnorPolynomial_coeff]
    exact hd
  constructor
  · intro ha
    obtain ⟨j, hj⟩ := (augmentSlot_eq_zero_iff 0 _).mp (hz 0) _ hc
    rw [milnorPairExponents_zero, ha, Finsupp.zero_apply] at hj
    exact hj rfl
  · intro hb
    obtain ⟨j, hj⟩ := (augmentSlot_eq_zero_iff 1 _).mp (hz 1) _ hc
    rw [milnorPairExponents_one, hb, Finsupp.zero_apply] at hj
    exact hj rfl

/-- A normalized polynomial comes from the span of actual tensor basis
elements with both factors reduced; this is not a new assumed subspace. -/
theorem cooperationTensor_mem_span_reduced_of_normalized (n : ℤ)
    (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n)
    (hz : ∀ j : Fin 2, augmentSlot j (cooperationTensorMilnorPolynomial H R B n z) = 0) :
    z ∈ Submodule.span F2
      (cooperationTensorMilnorBasis H R B n '' {d | d.2.1.val ≠ 0 ∧ d.2.2.val ≠ 0}) := by
  apply (cooperationTensorMilnorBasis H R B n).mem_span_image.mpr
  intro d hd
  exact cooperationTensorMilnorBasis_support_reduced H R B n z hz d
    (Finsupp.mem_support_iff.mp hd)

/-- Each allowed full tensor-basis term is the inclusion of a tensor of
the original reduced basis elements, with no change of representative. -/
theorem cooperationTensorMilnorBasis_positive (n : ℤ) (d : MilnorPair n)
    (h₀ : d.2.1.val ≠ 0) (h₁ : d.2.2.val ≠ 0) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    cooperationTensorMilnorBasis H R B n d = DirectSum.lof F2 ℤ _ d.1
      ((B.basis d.1 ⟨d.2.1.val, d.2.1.property, h₀⟩).val ⊗ₜ[F2]
        (B.basis (n - d.1) ⟨d.2.2.val, d.2.2.property, h₁⟩).val) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  rw [cooperationTensorMilnorBasis_apply]
  have hleft := cooperationMilnorBasis_reduced H R B d.1
    ⟨d.2.1.val, d.2.1.property, h₀⟩
  have hright := cooperationMilnorBasis_reduced H R B (n - d.1)
    ⟨d.2.2.val, d.2.2.property, h₁⟩
  rw [hleft, hright]
  rfl

/-- Actual reduced cooperations have normalized single-slot polynomials,
by their reduced basis rather than by any Adams-page assumption. -/
theorem cooperationMilnorPolynomial_reduced_normalized (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ (a : LinearMap.ker (cooperationCounitF2 H R n)) (j : Fin 1),
      augmentSlot j (cooperationMilnorPolynomial H R B n a.val) = 0 := by
  classical
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a j
  let f := (augmentSlot j).toLinearMap.comp
    ((cooperationMilnorPolynomial H R B n).comp (LinearMap.ker (cooperationCounitF2 H R n)).subtype)
  have hf : f = 0 := by
    apply (B.basis n).ext
    intro d
    change augmentSlot j (cooperationMilnorPolynomial H R B n (B.basis n d).val) = 0
    rw [cooperationMilnorPolynomial_reduced_basis]
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hex : ∃ i, d.val i ≠ 0 := by
      by_contra h
      apply d.property.2
      ext i
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hex
    have hinj : Function.Injective (fun k : ℕ => ((0 : Fin 1), k)) :=
      fun _ _ h => congrArg Prod.snd h
    have huses : UsesSlot (d.val.mapDomain (fun k => ((0 : Fin 1), k))) 0 := by
      refine ⟨i, ?_⟩
      simpa only [Finsupp.mapDomain_apply hinj] using hi
    rw [milnorMonomialPolynomial, augmentSlot_monomial, if_pos huses]
  exact LinearMap.congr_fun hf a

end
end KIP126.StableHomotopy.Cohomology
