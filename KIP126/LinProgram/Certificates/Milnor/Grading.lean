module

public import KIP126.LinProgram.Certificates.Milnor.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section


namespace MilnorCertificates
open scoped BigOperators

/-- A coordinate version of the existing weight, used only to prove grading. -/
def coordinateWeight (rank : Nat) (m : Monomial) : Nat :=
  ∑ j ∈ Finset.range rank, (m[j]?.getD 0) * (2^(j+1)-1)

theorem weight_eq_coordinateWeight (m : Monomial) :
    weight m = coordinateWeight m.length m := by
  unfold weight coordinateWeight
  rw [← List.sum_toFinset]
  · congr 1
    ext j
    simp
  · exact List.nodup_range

theorem generatorPower_length (rank index exponent : Nat) :
    (generatorPower rank index exponent).length = rank := by
  simp [generatorPower]

/-- A single coordinate has its expected polynomial degree. -/
theorem generatorPower_weight (rank index exponent : Nat) (hi : index ≤ rank) :
    weight (generatorPower rank index exponent) = exponent * (2^index-1) := by
  rw [weight_eq_coordinateWeight, generatorPower_length]
  unfold coordinateWeight generatorPower
  simp only [List.getElem?_map]
  by_cases hz : index = 0
  · subst index
    apply Finset.sum_eq_zero
    intro i hi
    have hir := Finset.mem_range.mp hi
    simp [hir]
  · have hpos : 0 < index := Nat.pos_of_ne_zero hz
    rw [Finset.sum_eq_single (index-1)]
    · have hm : index-1 < rank := by omega
      simp [hm, show index-1+1=index by omega]
    · intro j hj hne
      have hjr : j < rank := Finset.mem_range.mp hj
      have hji : j+1 ≠ index := by omega
      simp [hjr,hji]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- The binary coproduct split preserves polynomial degree arithmetically. -/
theorem binary_degree_split (k i : Nat) (hi : i ≤ k) :
    2^i * (2^(k-i)-1) + (2^i-1) = 2^k-1 := by
  have hpow : 2^i * 2^(k-i) = 2^k := by rw [← pow_add, Nat.add_sub_of_le hi]
  have hp : 0 < 2^(k-i) := Nat.two_pow_pos _
  have hpi : 0 < 2^i := Nat.two_pow_pos _
  have he : 2^i * (2^(k-i)-1) + 2^i = 2^k := by
    calc
      _ = 2^i * ((2^(k-i)-1)+1) := (Nat.mul_succ _ _).symm
      _ = 2^k := by rw [Nat.sub_add_cancel (by omega), hpow]
  omega

/-- Each actually enumerated term of Delta(xi_k) has total weight 2^k-1. -/
theorem generatorCoproduct_weight (rank k : Nat) (hk : k ≤ rank)
    (term : TensorMonomial) (ht : term ∈ generatorCoproduct rank k) :
    weight term.1 + weight term.2 = 2^k-1 := by
  simp only [generatorCoproduct, List.mem_map] at ht
  obtain ⟨i,hi,rfl⟩ := ht
  have hik : i ≤ k := by have := List.mem_range.mp hi; omega
  rw [generatorPower_weight rank (k-i) (2^i) (by omega),
    generatorPower_weight rank i 1 (by omega), one_mul]
  exact binary_degree_split k i hik

theorem multiplyMonomial_length (a b : Monomial) (h : a.length = b.length) :
    (multiplyMonomial a b).length = a.length := by
  simp [multiplyMonomial, h]

theorem multiplyMonomial_weight (a b : Monomial) (h : a.length = b.length) :
    weight (multiplyMonomial a b) = weight a + weight b := by
  rw [weight_eq_coordinateWeight, multiplyMonomial_length a b h,
    weight_eq_coordinateWeight a, weight_eq_coordinateWeight b, ← h]
  unfold coordinateWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have ha : j < a.length := Finset.mem_range.mp hj
  have hb : j < b.length := by omega
  simp [multiplyMonomial, ha, hb, Nat.add_mul]

/-- A homogeneous tensor list carries both arity and total grading. -/
def HomogeneousTensor (rank degree : Nat) (p : List TensorMonomial) : Prop :=
  ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank ∧ weight t.1 + weight t.2 = degree

theorem tensorMultiply_homogeneous (rank d e : Nat) (p q : List TensorMonomial)
    (hp : HomogeneousTensor rank d p) (hq : HomogeneousTensor rank e q) :
    HomogeneousTensor rank (d+e) (tensorMultiply p q) := by
  intro term ht
  simp only [tensorMultiply, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨x,hx,y,hy,rfl⟩ := ht
  obtain ⟨hx1,hx2,hxw⟩ := hp x hx
  obtain ⟨hy1,hy2,hyw⟩ := hq y hy
  have h1 : x.1.length = y.1.length := hx1.trans hy1.symm
  have h2 : x.2.length = y.2.length := hx2.trans hy2.symm
  refine ⟨(multiplyMonomial_length _ _ h1).trans hx1,
    (multiplyMonomial_length _ _ h2).trans hx2, ?_⟩
  rw [multiplyMonomial_weight _ _ h1, multiplyMonomial_weight _ _ h2]
  omega

theorem unitMonomial_weight (rank : Nat) : weight (unitMonomial rank) = 0 := by
  rw [weight_eq_coordinateWeight]
  unfold coordinateWeight unitMonomial
  apply Finset.sum_eq_zero
  intro j hj
  have h : j < rank := by simpa using hj
  simp [h]

theorem tensorUnit_homogeneous (rank : Nat) :
    HomogeneousTensor rank 0 [(unitMonomial rank,unitMonomial rank)] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst t
  exact ⟨by simp [unitMonomial], by simp [unitMonomial], by simp only [unitMonomial_weight, Nat.add_zero]⟩

theorem tensorPower_homogeneous (rank d : Nat) (p : List TensorMonomial)
    (hp : HomogeneousTensor rank d p) (n : Nat) :
    HomogeneousTensor rank (n*d) (tensorPower rank p n) := by
  induction n with
  | zero => simpa only [Nat.zero_mul, tensorPower] using tensorUnit_homogeneous rank
  | succ n ih =>
    simpa only [tensorPower, Nat.succ_mul] using tensorMultiply_homogeneous rank (n*d) d _ p ih hp

theorem generatorCoproduct_homogeneous (rank k : Nat) (hk : k ≤ rank) :
    HomogeneousTensor rank (2^k-1) (generatorCoproduct rank k) := by
  intro t ht
  refine ⟨?_,?_,generatorCoproduct_weight rank k hk t ht⟩
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact generatorPower_length _ _ _
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact generatorPower_length _ _ _

theorem fold_homogeneous (rank : Nat) (f : Nat → List TensorMonomial) (degree : Nat → Nat)
    (indices : List Nat) (initial : List TensorMonomial) (d : Nat)
    (hi : HomogeneousTensor rank d initial)
    (hf : ∀ j ∈ indices, HomogeneousTensor rank (degree j) (f j)) :
    HomogeneousTensor rank (d + (indices.map degree).sum)
      ((indices.map f).foldl tensorMultiply initial) := by
  induction indices generalizing initial d with
  | nil => simpa using hi
  | cons j js ih =>
    have hm := tensorMultiply_homogeneous rank d (degree j) initial (f j) hi (hf j (by simp))
    have hh := ih _ (d+degree j) hm (fun k hk => hf k (by simp [hk]))
    simpa [Nat.add_assoc] using hh

/-- Every term produced by the actual coproduct respects the input weight. -/
theorem coproduct_homogeneous (rank : Nat) (m : Monomial) (hm : m.length = rank) :
    HomogeneousTensor rank (weight m) (coproduct rank m) := by
  have hh := fold_homogeneous rank
    (fun j => tensorPower rank (generatorCoproduct rank (j+1)) (m[j]?.getD 0))
    (fun j => (m[j]?.getD 0)*(2^(j+1)-1)) (List.range rank)
    [(unitMonomial rank,unitMonomial rank)] 0 (tensorUnit_homogeneous rank)
    (fun j hj => tensorPower_homogeneous rank _ _
      (generatorCoproduct_homogeneous rank (j+1) (by have := List.mem_range.mp hj; omega)) _)
  simpa only [Nat.zero_add, coproduct, weight, hm] using hh

theorem coefficient_true_mem (p : Polynomial) (m : Monomial) (h : coefficient p m = true) : m ∈ p := by
  by_contra hn
  have hf : p.filter (· == m) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [beq_iff_eq]
    intro he
    exact hn (he ▸ hx)
  simp [coefficient, hf] at h

/-- Homogeneous inputs have no output coefficient in any different total degree.
The output monomial is arbitrary; no finite degree cutoff is assumed. -/
theorem product_degree_support (rank d e : Nat) (left right : Polynomial)
    (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (m : Monomial) (hm : m.length = rank) (hw : weight m ≠ d+e) :
    pairTensor left right (coproduct rank m) = false := by
  have hf : (coproduct rank m).filter
      (fun t => coefficient left t.1 && coefficient right t.2) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro term ht
    simp only [Bool.and_eq_true, not_and]
    intro ha hb
    have hd := hl term.1 (coefficient_true_mem left term.1 ha)
    have he := hr term.2 (coefficient_true_mem right term.2 hb)
    have hg := (coproduct_homogeneous rank m hm term ht).2.2
    exact hw (by omega)
  simp [pairTensor,hf]

/-- Rank-two Sq1 square vanishes on every monomial, with no degree bound.
The sole possible weight is two, forcing the monomial [2,0], where the two
coproduct contributions cancel. -/
theorem sqOne_square_unbounded_degree (m : Monomial) (hm : m.length = 2) :
    pairTensor [[1,0]] [[1,0]] (coproduct 2 m) = false := by
  by_cases hw : weight m = 2
  · cases m with
    | nil => simp at hm
    | cons a rest =>
      cases rest with
      | nil => simp at hm
      | cons b tail =>
        have ht : tail = [] := by simpa using hm
        subst tail
        have hw' : a + b*3 = 2 := by
          change a*1 + (b*3 + 0) = 2 at hw
          simpa only [Nat.mul_one, Nat.add_zero] using hw
        have ha : a = 2 := by omega
        have hb : b = 0 := by omega
        subst a
        subst b
        decide
  · apply product_degree_support 2 1 1 [[1,0]] [[1,0]] ?_ ?_ m hm hw
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      rfl
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      rfl

#print axioms coproduct_homogeneous
#print axioms product_degree_support
#print axioms sqOne_square_unbounded_degree

end MilnorCertificates
