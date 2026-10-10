import KIP126.LinProgram.Certificates.Milnor.FoldEvaluation

/-! Characteristic-two binary powers for the existing tensor-list semantics.
No original coproduct, multiplication, coefficient or product predicate changes. -/
namespace MilnorCertificates

def squareTensor (p : List TensorMonomial) : List TensorMonomial :=
  p.map fun t => (multiplyMonomial t.1 t.1, multiplyMonomial t.2 t.2)

theorem squareTensor_arity (rank : Nat) (p : List TensorMonomial)
    (hp : ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank) :
    ∀ t ∈ squareTensor p, t.1.length = rank ∧ t.2.length = rank := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact ⟨(multiplyMonomial_length _ _ rfl).trans (hp a ha).1,
    (multiplyMonomial_length _ _ rfl).trans (hp a ha).2⟩

variable {R : Type*} [CommRing R] [CharP R 2]

theorem tensorValue_square (left right : Nat → R) (p : List TensorMonomial) :
    tensorValue left right (squareTensor p) = (tensorValue left right p)^2 := by
  rw [show (2 : Nat) = 2^1 from rfl, tensorValue_frobenius]
  unfold squareTensor tensorValue
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply, monomialValue_multiply _ _ _ rfl,
    pow_one, pow_two]

def fastPower (rank : Nat) (p : List TensorMonomial) : Nat → List TensorMonomial
  | 0 => [(unitMonomial rank, unitMonomial rank)]
  | n+1 =>
    let squared := squareTensor (fastPower rank p ((n+1)/2))
    if (n+1)%2 = 0 then squared else tensorMultiply squared p
termination_by n => n
decreasing_by omega

theorem fastPower_arity (rank : Nat) (p : List TensorMonomial)
    (hp : ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank) (n : Nat) :
    ∀ t ∈ fastPower rank p n, t.1.length = rank ∧ t.2.length = rank := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fastPower, unitMonomial]
    | succ n =>
      rw [fastPower]
      have hs := squareTensor_arity rank _ (ih ((n+1)/2) (by omega))
      split
      · exact hs
      · exact tensorMultiply_arity rank _ _ hs hp

theorem tensorValue_fastPower (left right : Nat → R) (rank : Nat)
    (p : List TensorMonomial)
    (hp : ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank) (n : Nat) :
    tensorValue left right (fastPower rank p n) = (tensorValue left right p)^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fastPower, tensorValue, monomialValue_unit]
    | succ n =>
      rw [fastPower]
      have hhalf : (n+1)/2 < n+1 := by omega
      have hpower := ih ((n+1)/2) hhalf
      split
      · rename_i heven
        rw [tensorValue_square, hpower, ← pow_mul]
        congr 1
        omega
      · rename_i hodd
        rw [tensorValue_multiply left right _ p rank
          (squareTensor_arity rank _ (fastPower_arity rank p hp _)) hp,
          tensorValue_square, hpower, ← pow_mul, ← pow_succ]
        congr 1
        omega

def fastCoproduct (rank : Nat) (m : Monomial) : List TensorMonomial :=
  ((List.range rank).map fun j =>
    fastPower rank (generatorCoproduct rank (j+1)) (m[j]?.getD 0)).foldl
    tensorMultiply [(unitMonomial rank, unitMonomial rank)]

private theorem fold_arity (rank : Nat) (ps : List (List TensorMonomial))
    (acc : List TensorMonomial)
    (hp : ∀ p ∈ ps, ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank)
    (ha : ∀ t ∈ acc, t.1.length = rank ∧ t.2.length = rank) :
    ∀ t ∈ ps.foldl tensorMultiply acc, t.1.length = rank ∧ t.2.length = rank := by
  induction ps generalizing acc with
  | nil => exact ha
  | cons p ps ih =>
    exact ih _ (fun q hq => hp q (by simp [hq]))
      (tensorMultiply_arity rank acc p ha (hp p (by simp)))

theorem fastCoproduct_arity (rank : Nat) (m : Monomial) :
    ∀ t ∈ fastCoproduct rank m, t.1.length = rank ∧ t.2.length = rank := by
  apply fold_arity
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hg := generatorCoproduct_homogeneous rank (j+1)
      (by have := List.mem_range.mp hj; omega)
    exact fastPower_arity rank _ (fun t ht => ⟨(hg t ht).1, (hg t ht).2.1⟩) _
  · simp [unitMonomial]

theorem fastCoproduct_value (left right : Nat → R) (rank : Nat) (m : Monomial) :
    tensorValue left right (fastCoproduct rank m) =
      tensorValue left right (coproduct rank m) := by
  rw [coproduct_value]
  unfold fastCoproduct
  rw [tensorValue_fold left right rank _ _]
  · simp only [tensorValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      monomialValue_unit, mul_one, one_mul, add_zero, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    have hg := generatorCoproduct_homogeneous rank (j+1)
      (by have := List.mem_range.mp hj; omega)
    exact tensorValue_fastPower left right rank _
      (fun t ht => ⟨(hg t ht).1, (hg t ht).2.1⟩) _
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hg := generatorCoproduct_homogeneous rank (j+1)
      (by have := List.mem_range.mp hj; omega)
    exact fastPower_arity rank _ (fun t ht => ⟨(hg t ht).1, (hg t ht).2.1⟩) _
  · simp [unitMonomial]


end MilnorCertificates
