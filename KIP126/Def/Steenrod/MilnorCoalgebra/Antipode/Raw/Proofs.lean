module

public import KIP126.Def.Steenrod.MilnorCoalgebra.Antipode.Raw.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Grading.Proofs
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

/-! Properties of the fixed recursive polynomial maps. These are explicit
proof obligations, not additional choices of an antipode or its inverse. -/

namespace KIP126.Steenrod.Milnor.Coalgebra.Antipode

open KIP126.Core.Algebra
open scoped BigOperators

theorem generatorImage_zero : generatorImage 0 = 1 := by
  unfold generatorImage
  rw [Nat.strongRec_eq]
  simp

theorem generatorImage_rec (n : ℕ) (hn : 0 < n) :
    generatorImage n = xi 0 n + ∑ i : Fin n, if i.val = 0 then 0 else
      xi 0 (n - i.val) ^ (2 ^ i.val) * generatorImage i.val := by
  conv_lhs => unfold generatorImage
  rw [Nat.strongRec_eq]
  simp only [ne_of_gt hn, ↓reduceIte]
  rfl

theorem polynomialMap_xi (n : ℕ) : polynomialMap (xi 0 n) = generatorImage n := by
  cases n with
  | zero => simp [xi, generatorImage_zero]
  | succ n => simp [xi, polynomialMap]

/-- Every supported term retains the original integer internal degree. -/
theorem monomialImage_support_degree {n : ℤ} (m : MilnorMonomial n)
    (d : (Fin 1 × ℕ) →₀ ℕ) (hd : d ∈ (monomialImage m).support) :
    (slotWeight (slotExponentsEquiv 1 d 0) : ℤ) = n := by
  have hg (k : ℕ) : MvPolynomial.IsWeightedHomogeneous weight
      (generatorImage k) (2 ^ k - 1) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k = 0
      · subst k
        simpa [generatorImage_zero] using MvPolynomial.isWeightedHomogeneous_one F2 (@weight 1)
      rw [generatorImage_rec k (Nat.pos_of_ne_zero hk)]
      apply (homogeneous_xi (0 : Fin 1) k).add
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro i _
      split_ifs with hi
      · exact MvPolynomial.isWeightedHomogeneous_zero F2 _ _
      · have he : 2 ^ i.val * (2 ^ (k-i.val) - 1) + (2 ^ i.val - 1) = 2 ^ k - 1 := by
          have hp : 2 ^ (k-i.val) * 2 ^ i.val = 2 ^ k := by
            rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.isLt)]
          have h₁ : 1 ≤ 2 ^ (k-i.val) := Nat.one_le_pow _ _ (by omega)
          have h₂ : 1 ≤ 2 ^ i.val := Nat.one_le_pow _ _ (by omega)
          have h₃ : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
          nlinarith [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂, Nat.sub_add_cancel h₃]
        simpa only [nsmul_eq_mul, Nat.cast_id, he] using
          ((homogeneous_xi (0 : Fin 1) (k-i.val)).pow (2 ^ i.val)).mul (ih i.val i.isLt)
  have hm : MvPolynomial.IsWeightedHomogeneous weight (monomialPolynomial m)
      (slotWeight m.val) := by
    apply MvPolynomial.isWeightedHomogeneous_monomial
    simp [weight_eq_sum_slotWeight]
  have hr : MvPolynomial.IsWeightedHomogeneous weight (monomialImage m)
      (slotWeight m.val) := by
    apply homogeneous_aeval weight weight _ _ hm
    intro a
    exact hg (a.2+1)
  have he := hr (MvPolynomial.mem_support_iff.mp hd)
  have he' : slotWeight (slotExponentsEquiv 1 d 0) = slotWeight m.val := by
    simpa [weight_eq_sum_slotWeight] using he
  exact (congrArg (fun k : ℕ => (k : ℤ)) he').trans m.property

/-- The recursive formula solves `m (id ⊗ S) Δ = η ε` for the original Δ. -/
theorem rightConvolution_split (p : TensorPower 1) :
    rightConvolution (splitSlot (s := 1) 0 p) = polynomialAugmentation p := by
  have hzero (n : ℕ) : rightConvolution (xi (0 : Fin 2) n) = xi 0 n := by
    cases n <;> simp [xi, rightConvolution]
  have hone (n : ℕ) : rightConvolution (xi (1 : Fin 2) n) = generatorImage n := by
    cases n <;> simp [xi, rightConvolution, generatorImage_zero]
  have hh : rightConvolution.comp (splitSlot (s := 1) 0) = polynomialAugmentation := by
    apply MvPolynomial.algHom_ext
    intro a
    obtain ⟨a,n⟩ := a
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp only [AlgHom.comp_apply, polynomialAugmentation, MvPolynomial.aeval_X]
    simp only [splitSlot, MvPolynomial.aeval_X, ↓reduceIte, coproductGenerator,
      map_sum, map_mul, map_pow]
    change (∑ i ∈ Finset.range (n+2),
      rightConvolution (xi (0 : Fin 2) (n+1-i)) ^ (2^i) *
        rightConvolution (xi (1 : Fin 2) i)) = 0
    simp only [hzero, hone]
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, xi, one_pow, one_mul]
    rw [generatorImage_rec (n+1) (by omega)]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.sub_zero,
      pow_zero, pow_one, generatorImage_zero, mul_one, ↓reduceIte,
      Nat.add_one_ne_zero, zero_add]
    exact CharTwo.add_self_eq_zero _
  exact AlgHom.congr_fun hh p

/-- The same specified map also satisfies the left antipode equation. -/
theorem leftConvolution_split (p : TensorPower 1) :
    leftConvolution (splitSlot (s := 1) 0 p) = polynomialAugmentation p := by
  classical
  have hr (n : ℕ) :
      ∑ i ∈ Finset.range (n + 1), xi (0 : Fin 1) (n - i) ^ (2 ^ i) * generatorImage i =
        if n = 0 then 1 else 0 := by
    cases n with
    | zero => simp [xi, generatorImage_zero]
    | succ n =>
      have h := rightConvolution_split (xi (0 : Fin 1) (n + 1))
      have hzero (k : ℕ) : rightConvolution (xi (0 : Fin 2) k) = xi 0 k := by
        cases k <;> simp [xi, rightConvolution]
      have hone (k : ℕ) : rightConvolution (xi (1 : Fin 2) k) = generatorImage k := by
        cases k <;> simp [xi, rightConvolution, generatorImage_zero]
      simp only [xi, splitSlot, MvPolynomial.aeval_X, if_true,
        polynomialAugmentation] at h
      simp only [coproductGenerator, map_sum, map_mul, map_pow] at h
      change (∑ i ∈ Finset.range (n + 2),
        rightConvolution (xi (0 : Fin 2) (n+1-i)) ^ (2^i) *
          rightConvolution (xi (1 : Fin 2) i)) = 0 at h
      simpa only [hzero, hone, Nat.succ_ne_zero, if_false] using h
  have hl (n : ℕ) :
      ∑ i ∈ Finset.range (n + 1), generatorImage (n - i) ^ (2 ^ i) * xi (0 : Fin 1) i =
        if n = 0 then 1 else 0 := by
    let X : Matrix (Fin (n + 1)) (Fin (n + 1)) (TensorPower 1) :=
      fun i j => if i ≤ j then xi 0 (j.val - i.val) ^ (2 ^ i.val) else 0
    let S : Matrix (Fin (n + 1)) (Fin (n + 1)) (TensorPower 1) :=
      fun i j => if i ≤ j then generatorImage (j.val - i.val) ^ (2 ^ i.val) else 0
    have hsx : S * X = 1 := by
      ext i j
      by_cases hij : i ≤ j
      · have hsum : (S * X) i j =
            (∑ r ∈ Finset.range (j.val - i.val + 1),
              xi (0 : Fin 1) (j.val - i.val - r) ^ (2 ^ r) * generatorImage r) ^ (2 ^ i.val) := by
          rw [sum_pow_char_pow]
          change (∑ k, S i k * X k j) = _
          calc
            _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => i ≤ k ∧ k ≤ j),
                S i k * X k j := by
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro k _ hk
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hk
              by_cases hik : i ≤ k
              · simp [S, X, hik, hk hik]
              · simp [S, hik]
            _ = _ := by
              apply Finset.sum_bij (fun k _ => k.val - i.val)
              · intro k hk
                have hk' := (Finset.mem_filter.mp hk).2
                simp only [Finset.mem_range]
                omega
              · intro k hk l hl hkl
                have hk' := (Finset.mem_filter.mp hk).2
                have hl' := (Finset.mem_filter.mp hl).2
                apply Fin.ext
                omega
              · intro r hr
                have hr' := Finset.mem_range.mp hr
                refine ⟨⟨i.val + r, by omega⟩, ?_, ?_⟩
                · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
                  omega
                · simp
              · intro k hk
                obtain ⟨hik, hkj⟩ := (Finset.mem_filter.mp hk).2
                have hsub : j.val - i.val - (k.val - i.val) = j.val - k.val := by omega
                have hpow : 2 ^ k.val = 2 ^ (k.val - i.val) * 2 ^ i.val := by
                  rw [← pow_add]
                  congr 1
                  omega
                simp only [S, X, if_pos hik, if_pos hkj, mul_pow, ← pow_mul, hsub, hpow]
                exact mul_comm _ _
        rw [hsum, hr]
        by_cases heq : i = j
        · subst j
          simp
        · have hne : j.val - i.val ≠ 0 := by
            intro h
            apply heq
            apply Fin.ext
            omega
          simp [hne, heq]
      · rw [Matrix.mul_apply]
        rw [Finset.sum_eq_zero]
        · simp [show i ≠ j by intro h; exact hij h.le]
        · intro k _
          by_cases hik : i ≤ k
          · have hkj : ¬ k ≤ j := by omega
            simp [S, X, hkj]
          · simp [S, hik]
    have hxs : X * S = 1 := mul_eq_one_comm.mp hsx
    have hentry := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) (TensorPower 1) =>
      M 0 (Fin.last n)) hxs
    simp only [Matrix.mul_apply, X, S, Fin.zero_le, Fin.le_last, if_true,
      Fin.val_zero, Fin.val_last, Nat.sub_zero, pow_zero, pow_one] at hentry
    change (∑ x : Fin (n + 1), xi (0 : Fin 1) x.val * generatorImage (n-x.val) ^ (2^x.val)) =
      (if (0 : Fin (n+1)) = Fin.last n then 1 else 0) at hentry
    rw [Fin.sum_univ_eq_sum_range
      (fun k => xi (0 : Fin 1) k * generatorImage (n-k) ^ (2^k)) (n+1)] at hentry
    simpa [Matrix.one_apply, mul_comm, Fin.ext_iff, eq_comm] using hentry
  have hzero (n : ℕ) : leftConvolution (xi (0 : Fin 2) n) = generatorImage n := by
    cases n <;> simp [xi, leftConvolution, generatorImage_zero]
  have hone (n : ℕ) : leftConvolution (xi (1 : Fin 2) n) = xi 0 n := by
    cases n <;> simp [xi, leftConvolution]
  have hh : leftConvolution.comp (splitSlot (s := 1) 0) = polynomialAugmentation := by
    apply MvPolynomial.algHom_ext
    intro a
    obtain ⟨a,n⟩ := a
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp only [AlgHom.comp_apply, polynomialAugmentation, MvPolynomial.aeval_X]
    simp only [splitSlot, MvPolynomial.aeval_X, ↓reduceIte, coproductGenerator,
      map_sum, map_mul, map_pow]
    change (∑ i ∈ Finset.range (n+2),
      leftConvolution (xi (0 : Fin 2) (n+1-i)) ^ (2^i) *
        leftConvolution (xi (1 : Fin 2) i)) = 0
    simp only [hzero, hone]
    simpa using hl (n + 1)
  exact AlgHom.congr_fun hh p

/-- Milnor conjugation is involutive for this commutative polynomial algebra. -/
theorem polynomialMap_involutive (p : TensorPower 1) :
    polynomialMap (polynomialMap p) = p := by
  have hzero (n : ℕ) : leftConvolution (xi (0 : Fin 2) n) = generatorImage n := by
    cases n <;> simp [xi, leftConvolution, generatorImage_zero]
  have hone (n : ℕ) : leftConvolution (xi (1 : Fin 2) n) = xi 0 n := by
    cases n <;> simp [xi, leftConvolution]
  have hg (n : ℕ) : polynomialMap (generatorImage n) = xi (0 : Fin 1) n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [generatorImage_zero, xi]
      | succ n =>
        rw [generatorImage_rec (n+1) (by omega), map_add, map_sum, polynomialMap_xi]
        have hsum :
            (∑ i : Fin (n + 1), polynomialMap
              (if i.val = 0 then 0 else
                xi 0 (n + 1 - i.val) ^ (2 ^ i.val) * generatorImage i.val)) =
            ∑ i : Fin (n + 1), if i.val = 0 then 0 else
              generatorImage (n + 1 - i.val) ^ (2 ^ i.val) * xi 0 i.val := by
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> simp only [map_zero, map_mul, map_pow, polynomialMap_xi, ih i.val i.isLt]
        rw [hsum]
        have hleft := leftConvolution_split (xi (0 : Fin 1) (n+1))
        simp only [xi, splitSlot, MvPolynomial.aeval_X, if_true,
          polynomialAugmentation, coproductGenerator, map_sum, map_mul, map_pow] at hleft
        change (∑ i ∈ Finset.range (n+2),
          leftConvolution (xi (0 : Fin 2) (n+1-i)) ^ (2^i) *
            leftConvolution (xi (1 : Fin 2) i)) = 0 at hleft
        simp only [hzero, hone] at hleft
        rw [Finset.sum_range_succ] at hleft
        simp only [Nat.sub_self, generatorImage_zero, one_pow, one_mul] at hleft
        have heq := CharTwo.add_eq_zero.mp hleft
        rw [← Fin.sum_univ_eq_sum_range] at heq
        simpa only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.sub_zero,
          pow_zero, pow_one, xi, mul_one, ↓reduceIte, Nat.add_one_ne_zero, zero_add] using heq
  have hh : polynomialMap.comp polynomialMap = AlgHom.id F2 (TensorPower 1) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,n⟩
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change polynomialMap (polynomialMap (xi (0 : Fin 1) (n+1))) = xi 0 (n+1)
    rw [polynomialMap_xi, hg]
  exact AlgHom.congr_fun hh p

end KIP126.Steenrod.Milnor.Coalgebra.Antipode
