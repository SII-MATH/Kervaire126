module

public import KIP126.LinProgram.Certificates.Milnor.GeneratorEvaluation
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section


namespace MilnorCertificates
open scoped BigOperators

/-- Both iterated generator coproducts are indexed by three nonnegative
pieces of k. These two nested-pair encodings are related by (i,j)->(i+j,i). -/
def leftTriangle (k : Nat) : Finset (Nat × Nat) :=
  (Finset.range (k+1)).product (Finset.range (k+1)) |>.filter (fun p => p.1+p.2 ≤ k)
def rightTriangle (k : Nat) : Finset (Nat × Nat) :=
  (Finset.range (k+1)).product (Finset.range (k+1)) |>.filter (fun p => p.2 ≤ p.1)

theorem triangle_sum_reindex {R : Type*} [AddCommMonoid R] (k : Nat) (f : Nat → Nat → R) :
    ∑ p ∈ leftTriangle k, f p.1 p.2 =
      ∑ q ∈ rightTriangle k, f q.2 (q.1-q.2) := by
  apply Finset.sum_bij (fun p _ => (p.1+p.2,p.1))
  · intro p hp
    simp only [leftTriangle,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] at hp
    simp only [rightTriangle,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
    omega
  · intro a ha b hb he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> simp_all <;> omega
  · intro q hq
    simp only [rightTriangle,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] at hq
    refine ⟨(q.2,q.1-q.2),?_,?_⟩
    · simp only [leftTriangle,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
      omega
    · apply Prod.ext <;> simp <;> omega
  · intro p hp
    simp

/-- The two normal-form triple monomials agree after the explicit triangular
index change, including the iterated Frobenius exponent. -/
theorem triple_term_reindex {R : Type*} [CommRing R]
    (x y z : Nat → R) (k i j : Nat) (h : i+j ≤ k) :
    (x (k-i-j) ^ (2^j)) ^ (2^i) * (y j)^(2^i) * z i =
      x (k-(i+j))^(2^(i+j)) * (y ((i+j)-i))^(2^i) * z i := by
  rw [← pow_mul,← Nat.pow_add]
  have hsub : k-i-j=k-(i+j) := by omega
  have hji : i+j-i=j := by omega
  rw [hsub,hji,Nat.add_comm j i]

theorem triangular_frobenius_identity {R : Type*} [CommRing R]
    (x y z : Nat → R) (k : Nat) :
    (∑ p ∈ leftTriangle k,
      (x (k-p.1-p.2) ^ (2^p.2)) ^ (2^p.1) * y p.2 ^ (2^p.1) * z p.1) =
    ∑ q ∈ rightTriangle k,
      x (k-q.1) ^ (2^q.1) * y (q.1-q.2) ^ (2^q.2) * z q.2 := by
  rw [triangle_sum_reindex k (fun i j => (x (k-i-j) ^ (2^j)) ^ (2^i) * y j ^ (2^i) * z i)]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [rightTriangle,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_range] at hq
  have hsum : q.2 + (q.1-q.2) = q.1 := by omega
  rw [triple_term_reindex x y z k q.2 (q.1-q.2) (by omega),hsum]

theorem leftTriangle_nested {R : Type*} [AddCommMonoid R] (k : Nat) (f : Nat → Nat → R) :
    (∑ p ∈ leftTriangle k, f p.1 p.2) =
      ∑ i ∈ Finset.range (k+1), ∑ j ∈ Finset.range (k-i+1), f i j := by
  classical
  simp only [leftTriangle,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

theorem rightTriangle_nested {R : Type*} [AddCommMonoid R] (k : Nat) (f : Nat → Nat → R) :
    (∑ p ∈ rightTriangle k, f p.1 p.2) =
      ∑ i ∈ Finset.range (k+1), ∑ j ∈ Finset.range (i+1), f i j := by
  classical
  simp only [rightTriangle,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

#print axioms triangle_sum_reindex
#print axioms triangular_frobenius_identity
#print axioms leftTriangle_nested
#print axioms rightTriangle_nested

end MilnorCertificates
