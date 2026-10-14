module

public import KIP126.LinProgram.Certificates.Milnor.GeneratorEvaluation

@[expose] public section


namespace MilnorCertificates
variable {R : Type*} [CommRing R] [CharP R 2]

theorem tensorMultiply_arity (rank : Nat) (p q : List TensorMonomial)
    (hp : ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank)
    (hq : ∀ t ∈ q, t.1.length = rank ∧ t.2.length = rank) :
    ∀ t ∈ tensorMultiply p q, t.1.length = rank ∧ t.2.length = rank := by
  intro t ht
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
  have ha' := hp a ha
  have hb' := hq b hb
  exact ⟨(multiplyMonomial_length _ _ (ha'.1.trans hb'.1.symm)).trans ha'.1,
    (multiplyMonomial_length _ _ (ha'.2.trans hb'.2.symm)).trans ha'.2⟩

theorem tensorValue_fold (left right : Nat → R) (rank : Nat)
    (ps : List (List TensorMonomial)) (acc : List TensorMonomial)
    (hp : ∀ p ∈ ps, ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank)
    (ha : ∀ t ∈ acc, t.1.length = rank ∧ t.2.length = rank) :
    tensorValue left right (ps.foldl tensorMultiply acc) =
      tensorValue left right acc * (ps.map (tensorValue left right)).prod := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons,List.map_cons,List.prod_cons]
    rw [ih (tensorMultiply acc p) (fun q hq => hp q (by simp [hq]))
      (fun t ht => (tensorMultiply_arity rank acc p ha (hp p (by simp)) t ht)),
      tensorValue_multiply left right acc p rank ha (hp p (by simp)),mul_assoc]

theorem coproduct_value (left right : Nat → R) (rank : Nat) (m : Monomial) :
    tensorValue left right (coproduct rank m) =
      ((List.range rank).map fun j =>
        tensorValue left right (generatorCoproduct rank (j+1)) ^ (m[j]?.getD 0)).prod := by
  unfold coproduct
  rw [tensorValue_fold left right rank _ _]
  · simp only [tensorValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      monomialValue_unit,mul_one,one_mul,add_zero,List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    have hjr : j+1 ≤ rank := by have := List.mem_range.mp hj; omega
    exact tensorValue_power left right _ rank (2^(j+1)-1) _
      (generatorCoproduct_homogeneous rank (j+1) hjr)
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have hjr : j+1 ≤ rank := by have := List.mem_range.mp hj; omega
    intro t ht
    have h := tensorPower_homogeneous rank (2^(j+1)-1) _
      (generatorCoproduct_homogeneous rank (j+1) hjr) (m[j]?.getD 0) t ht
    exact ⟨h.1,h.2.1⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    simp [unitMonomial]

theorem coproduct_generatorPower_value (left right : Nat → R) (rank k exponent : Nat)
    (hk : k ≤ rank) (hk0 : k ≠ 0) :
    tensorValue left right (coproduct rank (generatorPower rank k exponent)) =
      tensorValue left right (generatorCoproduct rank k) ^ exponent := by
  rw [coproduct_value,← List.prod_toFinset _ List.nodup_range]
  rw [Finset.prod_eq_single (k-1)]
  · have hjr : k-1 < rank := by omega
    simp [generatorPower,hjr,show k-1+1=k by omega]
  · intro j hj hne
    have hjr : j < rank := by simpa using hj
    have hjk : j+1 ≠ k := by omega
    simp [generatorPower,hjr,hjk]
  · intro hn
    exact False.elim (hn (by simp; omega))

theorem coproduct_generatorZero_value (left right : Nat → R) (rank exponent : Nat) :
    tensorValue left right (coproduct rank (generatorPower rank 0 exponent)) = 1 := by
  rw [coproduct_value]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  have hjr := List.mem_range.mp hj
  simp [generatorPower,hjr]

#print axioms tensorValue_fold
#print axioms coproduct_value
#print axioms coproduct_generatorPower_value
end MilnorCertificates
