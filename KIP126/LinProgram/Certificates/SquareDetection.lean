import KIP126.LinProgram.Certificates.SquareDetection.Data
import Mathlib.Algebra.Polynomial.Degree.Domain

namespace KIP126.LinE2.SquareDetection

open KIP126.Core.Algebra

theorem u_cube : u ^ 3 = 0 := by
  rw [u, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem u_square_ne_zero : u ^ 2 ≠ 0 := by
  intro h
  have hm : (Polynomial.X : Polynomial F2) ^ 2 ∈
      Ideal.span {((Polynomial.X : Polynomial F2) ^ 3)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [u, map_pow] using h
  have hd := Polynomial.natDegree_le_of_dvd (Ideal.mem_span_singleton.mp hm)
    (pow_ne_zero 2 Polynomial.X_ne_zero)
  simp only [Polynomial.natDegree_X_pow] at hd
  omega

theorem u_pow_cap (n : ℕ) : u ^ min 3 n = u ^ n := by
  by_cases h : n ≤ 3
  · rw [min_eq_right h]
  · rw [min_eq_left (by omega), u_cube, pow_eq_zero_of_le (by omega : 3 ≤ n) u_cube]

theorem evaluate_X (i : Generator) :
    evaluate (MvPolynomial.X i) = if i = h6Generator then u else 0 := by
  simp [evaluate]

/-- The executable order computation agrees with the actual polynomial evaluation. -/
theorem evaluate_polynomialOfPowers (ns : List ℕ) :
    evaluate (polynomialOfPowers ns) = u ^ orderOfPowers ns := by
  induction ns using polynomialOfPowers.induct with
  | case1 => simp [polynomialOfPowers, orderOfPowers]
  | case2 i a rest h ih =>
    simp only [polynomialOfPowers, orderOfPowers, h, ↓reduceDIte, ↓reduceIte,
      map_mul, map_pow, evaluate_X, ih]
    by_cases hi : i = h6Generator.val
    · simp only [hi, ↓reduceIte, u_pow_cap, pow_add]
    · have he : (⟨i, h⟩ : Generator) ≠ h6Generator := fun he => hi (congrArg Fin.val he)
      simp only [hi, he, ↓reduceIte]
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha, u_cube]
  | case3 i a rest h => simp [polynomialOfPowers, orderOfPowers, h, u_cube]
  | case4 i => simp [polynomialOfPowers, orderOfPowers, u_cube]

theorem evaluate_monomialOfString (code : String) :
    evaluate (monomialOfString code) = u ^ monomialOrder code := by
  unfold monomialOfString monomialOrder
  split
  · simp
  · exact evaluate_polynomialOfPowers _

/-- A successful relation test is a kernel-proved sufficient condition, not
the existing unproved Gröbner normalization soundness assertion. -/
theorem relationCheck_sound (code : String) (h : relationCheck code = true) :
    evaluate (relationPolynomial code) = 0 := by
  rw [relationPolynomial, map_list_sum, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  have hm' := (List.all_eq_true.mp h) m hm
  change evaluate (monomialOfString m) = 0
  rw [evaluate_monomialOfString]
  exact pow_eq_zero_of_le (of_decide_eq_true hm') u_cube

/-- The artificial high-degree truncation also dies in the detector. -/
theorem evaluate_truncated_monomial (m : Generator →₀ ℕ)
    (h : 261 < (monomialDegree m).2) :
    evaluate (MvPolynomial.monomial m 1) = 0 := by
  by_cases hm : ∀ i : Generator, i ≠ h6Generator → m i = 0
  · have he : m = Finsupp.single h6Generator (m h6Generator) := by
      ext i
      by_cases hi : i = h6Generator
      · subst i; simp
      · simp [hi, hm i hi]
    have hd : (monomialDegree m).2 = m h6Generator * 64 := by
      conv_lhs => rw [he]
      simp [monomialDegree, h6Generator_degree]
    have hn : 3 ≤ m h6Generator := by rw [hd] at h; omega
    rw [he, ← MvPolynomial.X_pow_eq_monomial, map_pow, evaluate_X, if_pos rfl]
    exact pow_eq_zero_of_le hn u_cube
  · push Not at hm
    obtain ⟨i, hi, hmi⟩ := hm
    rw [evaluate, MvPolynomial.eval₂Hom_monomial]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hmi)
    simp [hi, zero_pow hmi]

/-- A certificate for the archived relations suffices to annihilate the whole
defining ideal, including the degree truncation. -/
theorem definingIdeal_le_ker
    (h : ∀ code ∈ RawData.relations, relationCheck code = true) :
    definingIdeal ≤ RingHom.ker evaluate := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with ⟨code, hc, rfl⟩ | ⟨m, hm, rfl⟩
  · exact relationCheck_sound code (h code hc)
  · exact evaluate_truncated_monomial m hm

/-- The square is nonzero as soon as the explicit finite relation certificate
is kernel-verified. No full basis theorem or Gröbner completeness is needed. -/
theorem dataH6Sq_ne_zero_of_relation_checks
    (h : ∀ code ∈ RawData.relations, relationCheck code = true) : dataH6Sq ≠ 0 := by
  intro hz
  have hz' : projection (MvPolynomial.X h6Generator ^ 2) = 0 := by
    have hh := congrArg Subtype.val hz
    simpa only [dataH6Sq, generator, projection, map_pow, ZeroMemClass.coe_zero] using hh
  have hi := Ideal.Quotient.eq_zero_iff_mem.mp hz'
  have he := definingIdeal_le_ker h hi
  change evaluate (MvPolynomial.X h6Generator ^ 2) = 0 at he
  rw [map_pow, evaluate_X, if_pos rfl] at he
  exact u_square_ne_zero he

theorem dataH6Sq_ne_zero_of_check (h : allRelationsCheck = true) : dataH6Sq ≠ 0 :=
  dataH6Sq_ne_zero_of_relation_checks (List.all_eq_true.mp h)

end KIP126.LinE2.SquareDetection
