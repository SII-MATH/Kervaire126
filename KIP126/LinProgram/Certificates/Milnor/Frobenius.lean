module

public import KIP126.LinProgram.Certificates.Milnor.Grading
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section


namespace MilnorCertificates

variable {R : Type*} [CommRing R] [CharP R 2]

def monomialValue (v : Nat → R) (m : Monomial) : R :=
  ((List.range m.length).map fun j => v j ^ (m[j]?.getD 0)).prod

def tensorValue (left right : Nat → R) (p : List TensorMonomial) : R :=
  (p.map fun t => monomialValue left t.1 * monomialValue right t.2).sum

/-- Frobenius in every characteristic-two commutative ring, at every 2-power. -/
theorem add_pow_two_power (x y : R) (n : Nat) :
    (x+y)^(2^n) = x^(2^n) + y^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ,pow_mul,ih,CharTwo.add_sq,← pow_mul,← pow_mul]

theorem list_sum_pow_two_power (p : List R) (n : Nat) :
    p.sum^(2^n) = (p.map fun x => x^(2^n)).sum := by
  induction p with
  | nil => simp
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,add_pow_two_power,ih]

/-- The actual tensor-list semantics obeys Frobenius, with all mixed expansion
terms cancelling in characteristic two. -/
theorem tensorValue_frobenius (left right : Nat → R) (p : List TensorMonomial) (n : Nat) :
    (tensorValue left right p)^(2^n) =
      (p.map fun t => (monomialValue left t.1)^(2^n) *
        (monomialValue right t.2)^(2^n)).sum := by
  unfold tensorValue
  rw [list_sum_pow_two_power,List.map_map]
  simp only [Function.comp_def,mul_pow]

theorem monomialValue_multiply (v : Nat → R) (a b : Monomial) (h : a.length = b.length) :
    monomialValue v (multiplyMonomial a b) = monomialValue v a * monomialValue v b := by
  unfold monomialValue
  rw [multiplyMonomial_length a b h,← h,← List.prod_map_mul]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  have ha : j < a.length := List.mem_range.mp hj
  have hb : j < b.length := by omega
  simp [multiplyMonomial,ha,hb,pow_add]

theorem tensorValue_multiply (left right : Nat → R) (p q : List TensorMonomial) (rank : Nat)
    (hp : ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank)
    (hq : ∀ t ∈ q, t.1.length = rank ∧ t.2.length = rank) :
    tensorValue left right (tensorMultiply p q) = tensorValue left right p * tensorValue left right q := by
  induction p with
  | nil => simp [tensorMultiply,tensorValue]
  | cons x xs ih =>
    have hx := hp x (by simp)
    have hxs : ∀ t ∈ xs, t.1.length = rank ∧ t.2.length = rank := fun t ht => hp t (by simp [ht])
    have happ (a b : List TensorMonomial) : tensorValue left right (a++b) =
        tensorValue left right a + tensorValue left right b := by simp [tensorValue]
    simp only [tensorMultiply,List.flatMap_cons,happ]
    change tensorValue left right (q.map (fun y => (multiplyMonomial x.1 y.1,multiplyMonomial x.2 y.2))) +
      tensorValue left right (tensorMultiply xs q) = _
    rw [ih hxs]
    have hh : tensorValue left right (q.map (fun y => (multiplyMonomial x.1 y.1,multiplyMonomial x.2 y.2))) =
        (monomialValue left x.1 * monomialValue right x.2) * tensorValue left right q := by
      unfold tensorValue
      rw [List.map_map,← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro y hy
      have hy' := hq y hy
      simp only [Function.comp_apply]
      rw [monomialValue_multiply _ _ _ (hx.1.trans hy'.1.symm),
        monomialValue_multiply _ _ _ (hx.2.trans hy'.2.symm)]
      simp only [mul_assoc,mul_left_comm]
    rw [hh]
    change _ = (monomialValue left x.1 * monomialValue right x.2 + tensorValue left right xs) * tensorValue left right q
    rw [add_mul]

theorem monomialValue_unit (v : Nat → R) (rank : Nat) :
    monomialValue v (unitMonomial rank) = 1 := by
  unfold monomialValue unitMonomial
  apply List.prod_eq_one
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  have h : j < rank := by simpa using hj
  simp [h]

theorem tensorValue_power (left right : Nat → R) (p : List TensorMonomial) (rank degree n : Nat)
    (hp : HomogeneousTensor rank degree p) :
    tensorValue left right (tensorPower rank p n) = (tensorValue left right p)^n := by
  induction n with
  | zero => simp [tensorPower,tensorValue,monomialValue_unit]
  | succ n ih =>
    rw [tensorPower,tensorValue_multiply left right _ p rank
      (fun t ht => ⟨(tensorPower_homogeneous rank degree p hp n t ht).1,
        (tensorPower_homogeneous rank degree p hp n t ht).2.1⟩)
      (fun t ht => ⟨(hp t ht).1,(hp t ht).2.1⟩),ih,pow_succ]

/-- Frobenius simplification is linked to the actual list expansion routine. -/
theorem tensorPower_frobenius (left right : Nat → R) (p : List TensorMonomial)
    (rank degree n : Nat) (hp : HomogeneousTensor rank degree p) :
    tensorValue left right (tensorPower rank p (2^n)) =
      (p.map fun t => (monomialValue left t.1)^(2^n) *
        (monomialValue right t.2)^(2^n)).sum := by
  rw [tensorValue_power left right p rank degree (2^n) hp,tensorValue_frobenius]

#print axioms tensorValue_frobenius

end MilnorCertificates
