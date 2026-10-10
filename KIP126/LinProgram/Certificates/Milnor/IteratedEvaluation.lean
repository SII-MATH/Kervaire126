import KIP126.LinProgram.Certificates.Milnor.FoldEvaluation
import KIP126.LinProgram.Certificates.Milnor.Coassociativity
import KIP126.LinProgram.Certificates.Milnor.TriangleReindex

namespace MilnorCertificates
variable {R : Type*} [CommRing R] [CharP R 2]

def tripleValue (x y z : Nat → R) (p : List TripleMonomial) : R :=
  (p.map fun t => monomialValue x t.1 * monomialValue y t.2.1 * monomialValue z t.2.2).sum

theorem sum_flatMap_value (p : List α) (f : α → List R) :
    (p.flatMap f).sum = (p.map fun a => (f a).sum).sum := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]

theorem tripleValue_left (x y z : Nat → R) (rank : Nat) (m : Monomial) :
    tripleValue x y z (coproductLeft rank m) =
      ((coproduct rank m).map fun t =>
        tensorValue x y (coproduct rank t.1) * monomialValue z t.2).sum := by
  unfold tripleValue coproductLeft
  rw [List.map_flatMap,sum_flatMap_value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [List.map_map,Function.comp_def,tensorValue]
  rw [List.sum_map_mul_right]

theorem tripleValue_right (x y z : Nat → R) (rank : Nat) (m : Monomial) :
    tripleValue x y z (coproductRight rank m) =
      ((coproduct rank m).map fun t =>
        monomialValue x t.1 * tensorValue y z (coproduct rank t.2)).sum := by
  unfold tripleValue coproductRight
  rw [List.map_flatMap,sum_flatMap_value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [List.map_map,Function.comp_def,tensorValue,mul_assoc]
  rw [List.sum_map_mul_left]

def deltaValue (x y : Nat → R) (rank : Nat) (j : Nat) : R :=
  tensorValue x y (generatorCoproduct rank (j+1))

theorem coproduct_value_monomial (x y : Nat → R) (rank : Nat) (m : Monomial)
    (hm : m.length = rank) :
    tensorValue x y (coproduct rank m) = monomialValue (deltaValue x y rank) m := by
  rw [coproduct_value]
  simp only [monomialValue,hm,deltaValue]

theorem tripleValue_left_substitute (x y z : Nat → R) (rank : Nat) (m : Monomial)
    (hm : m.length = rank) :
    tripleValue x y z (coproductLeft rank m) =
      tensorValue (deltaValue x y rank) z (coproduct rank m) := by
  rw [tripleValue_left]
  unfold tensorValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have h := coproduct_homogeneous rank m hm t ht
  rw [← tensorValue, coproduct_value_monomial x y rank t.1 h.1]

theorem tripleValue_right_substitute (x y z : Nat → R) (rank : Nat) (m : Monomial)
    (hm : m.length = rank) :
    tripleValue x y z (coproductRight rank m) =
      tensorValue x (deltaValue y z rank) (coproduct rank m) := by
  rw [tripleValue_right]
  unfold tensorValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have h := coproduct_homogeneous rank m hm t ht
  rw [← tensorValue, coproduct_value_monomial y z rank t.2 h.2.1]

theorem xiValue_delta (x y : Nat → R) (rank k : Nat) (hk : k ≤ rank) :
    xiValue (deltaValue x y rank) k =
      ((List.range (k+1)).map fun i => xiValue x (k-i) ^ (2^i) * xiValue y i).sum := by
  by_cases hz : k = 0
  · subst k
    simp [xiValue]
  · simp only [xiValue,hz,ite_false,deltaValue]
    rw [show k-1+1=k by omega,generatorCoproduct_value x y rank k hk]
    rfl

theorem list_range_sum (n : Nat) (f : Nat → R) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.sum_toFinset f (List.nodup_range (n := n))]
  congr 1
  ext i
  simp

theorem generator_substitute_left (x y z : Nat → R) (rank k : Nat) (hk : k ≤ rank) :
    tensorValue (deltaValue x y rank) z (generatorCoproduct rank k) =
      ∑ i ∈ Finset.range (k+1), ∑ j ∈ Finset.range (k-i+1),
        (xiValue x (k-i-j) ^ (2^j)) ^ (2^i) * xiValue y j ^ (2^i) * xiValue z i := by
  rw [generatorCoproduct_value _ _ rank k hk,list_range_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [xiValue_delta x y rank (k-i) (by omega),list_sum_pow_two_power,List.map_map]
  rw [← List.sum_map_mul_right,list_range_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.comp_apply,mul_pow]

theorem generator_substitute_right (x y z : Nat → R) (rank k : Nat) (hk : k ≤ rank) :
    tensorValue x (deltaValue y z rank) (generatorCoproduct rank k) =
      ∑ i ∈ Finset.range (k+1), ∑ j ∈ Finset.range (i+1),
        xiValue x (k-i) ^ (2^i) * xiValue y (i-j) ^ (2^j) * xiValue z j := by
  rw [generatorCoproduct_value _ _ rank k hk,list_range_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i ≤ rank := by have := Finset.mem_range.mp hi; omega
  rw [xiValue_delta y z rank i hir,← List.sum_map_mul_left,list_range_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (mul_assoc _ _ _).symm

/-- Equality of the two generator substitutions propagates through every
monomial of the actual executable coproduct. -/
theorem tripleValue_eq_of_generators (x y z : Nat → R) (rank : Nat)
    (hgen : ∀ j < rank,
      tensorValue (deltaValue x y rank) z (generatorCoproduct rank (j+1)) =
        tensorValue x (deltaValue y z rank) (generatorCoproduct rank (j+1)))
    (m : Monomial) (hm : m.length = rank) :
    tripleValue x y z (coproductLeft rank m) =
      tripleValue x y z (coproductRight rank m) := by
  rw [tripleValue_left_substitute x y z rank m hm,
    tripleValue_right_substitute x y z rank m hm,coproduct_value,coproduct_value]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  rw [hgen j (List.mem_range.mp hj)]

/-- Arbitrary generator index: no finite-degree or rank-three enumeration. -/
theorem generator_delta_coassociative (x y z : Nat → R) (rank k : Nat) (hk : k ≤ rank) :
    tensorValue (deltaValue x y rank) z (generatorCoproduct rank k) =
      tensorValue x (deltaValue y z rank) (generatorCoproduct rank k) := by
  rw [generator_substitute_left x y z rank k hk,generator_substitute_right x y z rank k hk]
  have h := triangular_frobenius_identity (xiValue x) (xiValue y) (xiValue z) k
  rw [leftTriangle_nested k (fun i j => (xiValue x (k-i-j) ^ (2^j)) ^ (2^i) * xiValue y j ^ (2^i) * xiValue z i),
    rightTriangle_nested k (fun i j => xiValue x (k-i) ^ (2^i) * xiValue y (i-j) ^ (2^j) * xiValue z j)] at h
  exact h

/-- Coassociativity of the actual executable expansions under every
characteristic-two commutative-ring valuation, for every rank and monomial. -/
theorem tripleValue_coassociative (x y z : Nat → R) (rank : Nat)
    (m : Monomial) (hm : m.length = rank) :
    tripleValue x y z (coproductLeft rank m) =
      tripleValue x y z (coproductRight rank m) := by
  apply tripleValue_eq_of_generators x y z rank _ m hm
  intro j hj
  exact generator_delta_coassociative x y z rank (j+1) (by omega)

#print axioms generator_delta_coassociative
#print axioms tripleValue_coassociative
end MilnorCertificates
