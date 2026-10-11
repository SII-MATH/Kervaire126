module

public import KIP126.LinProgram.Certificates.Secondary.Expansion

@[expose] public section


namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- Monomial contraction in the original Milnor coordinates. A failed subtraction is
an algebraic zero, and a rank mismatch is rejected rather than truncated. -/
def contractMonomial : Monomial → Monomial → Option Monomial
  | [], [] => some []
  | factor :: factors, value :: values =>
      if factor ≤ value then
        (contractMonomial factors values).map ((value - factor) :: ·)
      else none
  | _, _ => none

theorem contractMonomial_eq_some (factor input output : Monomial)
    (hrank : output.length = factor.length) :
    contractMonomial factor input = some output ↔ multiplyMonomial factor output = input := by
  induction factor generalizing input output with
  | nil =>
    cases output with
    | nil => cases input <;> simp [contractMonomial, multiplyMonomial]
    | cons x xs => simp at hrank
  | cons f fs ih =>
    cases output with
    | nil => simp at hrank
    | cons y ys =>
      have hlen : ys.length = fs.length := by simpa using hrank
      cases input with
      | nil => simp [contractMonomial, multiplyMonomial]
      | cons x xs =>
        by_cases hfx : f ≤ x
        · simp only [contractMonomial, hfx, ↓reduceIte, multiplyMonomial,
            List.zipWith_cons_cons, List.cons.injEq]
          rw [Option.map_eq_some_iff]
          constructor
          · rintro ⟨rest, hrest, he⟩
            have he' : x - f = y ∧ rest = ys := List.cons.inj he
            rcases he' with ⟨heq, rfl⟩
            exact ⟨by omega, (ih xs _ hlen).mp hrest⟩
          · rintro ⟨he, ht⟩
            refine ⟨ys, (ih xs ys hlen).mpr ht, ?_⟩
            congr 1
            omega
        · have hne : f + y ≠ x := by omega
          simp [contractMonomial, hfx, multiplyMonomial, hne]

theorem contractMonomial_length (factor input output : Monomial)
    (h : contractMonomial factor input = some output) :
    output.length = factor.length ∧ input.length = factor.length := by
  induction factor generalizing input output with
  | nil =>
    cases input with
    | nil => simp only [contractMonomial, Option.some.injEq] at h; subst output; simp
    | cons x xs => simp [contractMonomial] at h
  | cons f fs ih =>
    cases input with
    | nil => simp [contractMonomial] at h
    | cons x xs =>
      by_cases hfx : f ≤ x
      · simp only [contractMonomial, hfx, ↓reduceIte, Option.map_eq_some_iff] at h
        rcases h with ⟨rest, hrest, rfl⟩
        have ht := ih xs rest hrest
        simp [ht.1, ht.2]
      · simp [contractMonomial, hfx] at h

theorem contractMonomial_eq_none_of_length_ne (factor input : Monomial)
    (h : input.length ≠ factor.length) : contractMonomial factor input = none := by
  cases hc : contractMonomial factor input with
  | none => rfl
  | some output => exact False.elim (h (contractMonomial_length factor input output hc).2)

theorem contractMonomial_eq_none_iff (factor input : Monomial) :
    contractMonomial factor input = none ↔
      ∀ output, output.length = factor.length → multiplyMonomial factor output ≠ input := by
  constructor
  · intro hn output hl he
    have hs := (contractMonomial_eq_some factor input output hl).mpr he
    rw [hn] at hs
    cases hs
  · intro h
    cases hc : contractMonomial factor input with
    | none => rfl
    | some output =>
      have hl := (contractMonomial_length factor input output hc).1
      exact False.elim (h output hl ((contractMonomial_eq_some factor input output hl).mp hc))

/-- F₂ linear extension of the dual monomial contraction, preserving multiplicities. -/
def contractPolynomial (factor : Monomial) (p : Polynomial) : Polynomial :=
  p.filterMap (contractMonomial factor)

theorem coefficient_cons (a : Monomial) (p : Polynomial) (m : Monomial) :
    coefficient (a :: p) m = xor (decide (a = m)) (coefficient p m) := by
  change coefficient ([a] ++ p) m = _
  rw [coefficient_append]
  congr 1
  by_cases h : a = m <;> simp [coefficient, h]

/-- All coefficients of the executable contraction are the adjoint of multiplication
by the factor in the original polynomial-coordinate algebra, with no degree bound. -/
theorem contractPolynomial_coefficient (factor : Monomial) (p : Polynomial)
    (m : Monomial) (hrank : m.length = factor.length) :
    coefficient (contractPolynomial factor p) m =
      coefficient p (multiplyMonomial factor m) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases hc : contractMonomial factor a with
    | none =>
      have hne : a ≠ multiplyMonomial factor m := by
        intro he
        have hs := (contractMonomial_eq_some factor a m hrank).mpr he.symm
        rw [hc] at hs
        cases hs
      simp only [contractPolynomial, List.filterMap_cons, hc, coefficient_cons,
        decide_eq_false hne, Bool.false_xor]
      exact ih
    | some b =>
      have heq : (b = m) ↔ a = multiplyMonomial factor m := by
        constructor
        · intro he; subst b
          exact ((contractMonomial_eq_some factor a m hrank).mp hc).symm
        · intro he
          have hs := (contractMonomial_eq_some factor a m hrank).mpr he.symm
          exact Option.some.inj (hc.symm.trans hs)
      simp only [contractPolynomial, List.filterMap_cons, hc, coefficient_cons]
      change xor (decide (b = m)) (coefficient (contractPolynomial factor p) m) = _
      rw [ih]
      simp only [heq]

theorem multiplyMonomial_comm (a b : Monomial) :
    multiplyMonomial a b = multiplyMonomial b a :=
  List.zipWith_comm_of_comm Nat.add_comm

theorem multiplyMonomial_assoc (a b c : Monomial) :
    multiplyMonomial (multiplyMonomial a b) c = multiplyMonomial a (multiplyMonomial b c) := by
  induction a generalizing b c with
  | nil => rfl
  | cons a as ih =>
    cases b with
    | nil => rfl
    | cons b bs =>
      cases c with
      | nil => rfl
      | cons c cs =>
        change ((a + b) + c) :: multiplyMonomial (multiplyMonomial as bs) cs =
          (a + (b + c)) :: multiplyMonomial as (multiplyMonomial bs cs)
        rw [Nat.add_assoc, ih]

/-- Two contractions are the contraction by the product of their dual factors. -/
theorem contractPolynomial_twice_coefficient (first second : Monomial) (p : Polynomial)
    (m : Monomial) (hfs : first.length = second.length) (hm : m.length = second.length) :
    coefficient (contractPolynomial second (contractPolynomial first p)) m =
      coefficient (contractPolynomial (multiplyMonomial first second) p) m := by
  rw [contractPolynomial_coefficient second _ m hm]
  rw [contractPolynomial_coefficient first p (multiplyMonomial second m)
    (by rw [multiplyMonomial_length second m hm.symm]; exact hfs.symm)]
  rw [contractPolynomial_coefficient (multiplyMonomial first second) p m
    (by rw [multiplyMonomial_length first second hfs]; exact hm.trans hfs.symm)]
  rw [multiplyMonomial_assoc]

/-- The native `Contr(0,k,-)` is the identity because xi_0 is 1. -/
theorem contractPolynomial_xi_zero_coefficient (rank exponent : Nat) (p : Polynomial)
    (m : Monomial) (hm : m.length = rank) :
    coefficient (contractPolynomial (generatorPower rank 0 exponent) p) m = coefficient p m := by
  rw [contractPolynomial_coefficient _ p m (by rw [generatorPower_length]; exact hm)]
  have hz : generatorPower rank 0 exponent = unitMonomial rank := by
    simp [generatorPower, unitMonomial]
  rw [hz, multiplyMonomial_comm, multiply_unit_right m rank hm]

/-- A power factor uses exactly the existing dual generator coordinates. -/
theorem contractPolynomial_generatorPower_coefficient (rank index power : Nat)
    (p : Polynomial) (m : Monomial) (hm : m.length = rank) :
    coefficient (contractPolynomial (generatorPower rank index (2 ^ power)) p) m =
      coefficient p (multiplyMonomial (generatorPower rank index (2 ^ power)) m) :=
  contractPolynomial_coefficient _ p m (by rw [generatorPower_length]; exact hm)

def contractModuleExpression (factor : Monomial) (a : ModuleExpression) : ModuleExpression :=
  a.filterMap fun term => (contractMonomial factor term.sq).map fun sq => ⟨sq, term.generator⟩

theorem contractModuleExpression_coefficient (factor : Monomial) (a : ModuleExpression)
    (target : Nat) (m : Monomial) (hm : m.length = factor.length) :
    expressionCoefficient (contractModuleExpression factor a) target m =
      expressionCoefficient a target (multiplyMonomial factor m) := by
  induction a with
  | nil => rfl
  | cons term a ih =>
    cases hc : contractMonomial factor term.sq with
    | none =>
      have hne : term.sq ≠ multiplyMonomial factor m := by
        intro he
        have hs := (contractMonomial_eq_some factor term.sq m hm).mpr he.symm
        rw [hc] at hs
        cases hs
      simp only [contractModuleExpression, List.filterMap_cons, hc, Option.map_none]
      rw [expressionCoefficient_cons]
      simp only [hne, and_false, decide_false, Bool.false_xor]
      exact ih
    | some b =>
      have heq : (b = m) ↔ term.sq = multiplyMonomial factor m := by
        constructor
        · intro he; subst b
          exact ((contractMonomial_eq_some factor term.sq m hm).mp hc).symm
        · intro he
          have hs := (contractMonomial_eq_some factor term.sq m hm).mpr he.symm
          exact Option.some.inj (hc.symm.trans hs)
      simp only [contractModuleExpression, List.filterMap_cons, hc, Option.map_some]
      rw [expressionCoefficient_cons, expressionCoefficient_cons]
      change xor (decide (term.generator = target ∧ b = m))
        (expressionCoefficient (contractModuleExpression factor a) target m) = _
      rw [ih]
      simp only [heq]

/-- Successful contraction removes precisely the dual factor's original weight. -/
theorem contractMonomial_weight (factor input output : Monomial)
    (h : contractMonomial factor input = some output) :
    weight input = weight factor + weight output := by
  have hl := contractMonomial_length factor input output h
  rw [← (contractMonomial_eq_some factor input output hl.1).mp h]
  exact multiplyMonomial_weight factor output hl.1.symm

/-- Excess degree is an actual algebraic zero, at every rank. -/
theorem contractMonomial_eq_none_of_weight_lt (factor input : Monomial)
    (h : weight input < weight factor) : contractMonomial factor input = none := by
  cases hc : contractMonomial factor input with
  | none => rfl
  | some output =>
    have hw := contractMonomial_weight factor input output hc
    omega

theorem contractGeneratorPower_eq_none_of_weight_lt (rank index exponent : Nat)
    (input : Monomial) (hi : index ≤ rank)
    (h : weight input < exponent * (2 ^ index - 1)) :
    contractMonomial (generatorPower rank index exponent) input = none := by
  apply contractMonomial_eq_none_of_weight_lt
  rwa [generatorPower_weight rank index exponent hi]

/-- The first contraction in every native A₂ summand with outer index m costs
at least 2^(m-1), independently of the remaining path and both inner indices. -/
theorem outerContraction_factor_weight_lower (rank m k : Nat)
    (hkm : k < m) (hm : m ≤ rank) :
    2 ^ (m - 1) ≤ weight (generatorPower rank (m - k) (2 ^ k)) := by
  rw [generatorPower_weight rank (m-k) (2^k) (by omega)]
  have hpow : 2 ^ k * 2 ^ (m-k) = 2 ^ m := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hkpow : 2 ^ k ≤ 2 ^ (m-1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmpos : 0 < m := by omega
  have hdouble : 2 ^ m = 2 ^ (m-1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, hpow]
  omega

theorem outerContraction_eq_none_of_weight_lt (rank m k : Nat) (input : Monomial)
    (hkm : k < m) (hm : m ≤ rank) (hw : weight input < 2 ^ (m-1)) :
    contractMonomial (generatorPower rank (m-k) (2^k)) input = none := by
  apply contractMonomial_eq_none_of_weight_lt
  exact lt_of_lt_of_le hw (outerContraction_factor_weight_lower rank m k hkm hm)

end KIP126.Computation.Secondary
