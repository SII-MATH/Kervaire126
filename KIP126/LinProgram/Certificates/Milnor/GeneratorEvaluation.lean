module

public import KIP126.LinProgram.Certificates.Milnor.Frobenius

@[expose] public section


namespace MilnorCertificates
open scoped BigOperators
variable {R : Type*} [CommRing R] [CharP R 2]

/-- xi_0 is the unit; xi_(j+1) is coordinate j. -/
def xiValue (v : Nat → R) (index : Nat) : R := if index = 0 then 1 else v (index-1)

theorem generatorPower_value (v : Nat → R) (rank index exponent : Nat) (hi : index ≤ rank) :
    monomialValue v (generatorPower rank index exponent) = (xiValue v index)^exponent := by
  unfold monomialValue
  rw [generatorPower_length]
  rw [← List.prod_toFinset _ List.nodup_range]
  by_cases hz : index = 0
  · subst index
    simp only [xiValue,ite_true,one_pow]
    apply Finset.prod_eq_one
    intro j hj
    have hjr : j < rank := by simpa using hj
    simp [generatorPower,hjr]
  · rw [Finset.prod_eq_single (index-1)]
    · have hjr : index-1 < rank := by omega
      simp [generatorPower,hjr,xiValue,hz,show index-1+1=index by omega]
    · intro j hj hne
      have hjr : j < rank := by simpa using hj
      have hji : j+1 ≠ index := by omega
      simp [generatorPower,hjr,hji]
    · intro hn
      exact False.elim (hn (by simp; omega))

/-- The explicit generator coproduct evaluates to the standard Milnor sum,
uniformly in every generator index and ambient rank. -/
theorem generatorCoproduct_value (left right : Nat → R) (rank k : Nat) (hk : k ≤ rank) :
    tensorValue left right (generatorCoproduct rank k) =
      ((List.range (k+1)).map fun i => (xiValue left (k-i))^(2^i) * xiValue right i).sum := by
  unfold tensorValue generatorCoproduct
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hik : i ≤ k := by have := List.mem_range.mp hi; omega
  simp only [Function.comp_apply]
  rw [generatorPower_value left rank (k-i) (2^i) (by omega),
    generatorPower_value right rank i 1 (by omega),pow_one]

/-- Frobenius of any generator coproduct, connected to the actual tensorPower
routine rather than a postulated polynomial formula. -/
theorem generatorCoproduct_frobenius (left right : Nat → R) (rank k n : Nat) (hk : k ≤ rank) :
    tensorValue left right (tensorPower rank (generatorCoproduct rank k) (2^n)) =
      (((List.range (k+1)).map fun i =>
        ((xiValue left (k-i))^(2^i) * xiValue right i)^(2^n))).sum := by
  rw [tensorValue_power left right _ rank (2^k-1) (2^n)
    (generatorCoproduct_homogeneous rank k hk),generatorCoproduct_value left right rank k hk,
    list_sum_pow_two_power,List.map_map]
  rfl

#print axioms generatorCoproduct_value
#print axioms generatorCoproduct_frobenius

end MilnorCertificates
