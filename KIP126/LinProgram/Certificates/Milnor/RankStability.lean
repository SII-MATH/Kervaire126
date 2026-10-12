module

public import KIP126.LinProgram.Certificates.Milnor.WindowSoundness

@[expose] public section


namespace MilnorCertificates
open scoped BigOperators

/-- The contribution of any coordinate is bounded by total degree. -/
theorem weighted_coordinate_le (m : Monomial) (j : Nat) (hj : j < m.length) :
    m[j]*(2^(j+1)-1) ≤ weight m := by
  rw [weight_eq_coordinateWeight]
  unfold coordinateWeight
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range m.length) =>
    Nat.zero_le ((m[i]?.getD 0)*(2^(i+1)-1))) (Finset.mem_range.mpr hj)
  simpa [hj] using hh

/-- No coordinate of degree greater than the bound can occur in a bounded
monomial. This is derived from actual weight, without a support assumption. -/
theorem high_coordinate_zero (m : Monomial) (bound j : Nat) (hj : j < m.length)
    (hw : weight m ≤ bound) (hhigh : bound < 2^(j+1)-1) : m[j] = 0 := by
  have hc := (weighted_coordinate_le m j hj).trans hw
  by_contra hn
  have hp : 1 ≤ m[j] := by omega
  have hm := Nat.mul_le_mul_right (2^(j+1)-1) hp
  simp only [Nat.one_mul] at hm
  omega

/-- Once rank r captures every generator degree <= bound, all later
coordinates of any higher-rank bounded monomial vanish. -/
theorem coordinates_above_rank_zero (m : Monomial) (rank bound j : Nat)
    (hj : j < m.length) (hrj : rank ≤ j) (hw : weight m ≤ bound)
    (henough : bound < 2^(rank+1)-1) : m[j] = 0 := by
  apply high_coordinate_zero m bound j hj hw
  have hp : 2^(rank+1) ≤ 2^(j+1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

def pad (m : Monomial) : Monomial := m ++ [0]

theorem pad_weight (m : Monomial) : weight (pad m) = weight m := by
  rw [weight_eq_coordinateWeight, weight_eq_coordinateWeight]
  simp only [pad, List.length_append, List.length_singleton]
  unfold coordinateWeight
  rw [Finset.sum_range_succ]
  have hz : ((m ++ [0])[m.length]?.getD 0)*(2^(m.length+1)-1) = 0 := by simp
  rw [hz, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Finset.mem_range.mp hj
  have he : (m ++ [0])[j]? = m[j]? := List.getElem?_append_left h
  rw [he]

theorem bounded_succ_is_pad (m : Monomial) (rank bound : Nat)
    (hm : m.length = rank+1) (hw : weight m ≤ bound)
    (henough : bound < 2^(rank+1)-1) : m = pad (m.take rank) := by
  have hx : m[rank]'(by omega) = 0 := high_coordinate_zero m bound rank (by omega) hw henough
  have hd : m.drop rank = [0] := by
    apply List.ext_getElem
    · simp [hm]
    · intro i hi hj
      have hi0 : i = 0 := by simp at hj; omega
      subst i
      simpa using hx
  calc
    m = m.take rank ++ m.drop rank := (List.take_append_drop rank m).symm
    _ = pad (m.take rank) := by rw [hd]; rfl

def padTensor (t : TensorMonomial) : TensorMonomial := (pad t.1,pad t.2)

theorem generatorPower_pad (rank k exponent : Nat) (hk : k ≤ rank) :
    generatorPower (rank+1) k exponent = pad (generatorPower rank k exponent) := by
  simp only [generatorPower, List.range_succ, List.map_append, List.map_singleton, pad]
  have hn : rank+1 ≠ k := by omega
  simp only [hn, if_false]

theorem generatorCoproduct_pad (rank k : Nat) (hk : k ≤ rank) :
    generatorCoproduct (rank+1) k = (generatorCoproduct rank k).map padTensor := by
  unfold generatorCoproduct
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hik : i ≤ k := by have := List.mem_range.mp hi; omega
  simp only [Function.comp_apply, padTensor, generatorPower_pad rank (k-i) _ (by omega),
    generatorPower_pad rank i _ (by omega)]

theorem multiplyMonomial_pad (a b : Monomial) (h : a.length = b.length) :
    multiplyMonomial (pad a) (pad b) = pad (multiplyMonomial a b) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [multiplyMonomial,pad]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      change (x+y) :: multiplyMonomial (pad xs) (pad ys) =
        (x+y) :: pad (multiplyMonomial xs ys)
      rw [ih ys (by simpa using h)]

def TensorArity (rank : Nat) (p : List TensorMonomial) : Prop :=
  ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank

theorem tensorMultiply_pad (rank : Nat) (p q : List TensorMonomial)
    (hp : TensorArity rank p) (hq : TensorArity rank q) :
    tensorMultiply (p.map padTensor) (q.map padTensor) =
      (tensorMultiply p q).map padTensor := by
  unfold tensorMultiply
  simp only [List.flatMap_map, List.map_flatMap, List.map_map]
  apply List.flatMap_congr
  intro x hx
  apply List.map_congr_left
  intro y hy
  obtain ⟨hx1,hx2⟩ := hp x hx
  obtain ⟨hy1,hy2⟩ := hq y hy
  simp only [Function.comp_apply,padTensor]
  rw [multiplyMonomial_pad _ _ (hx1.trans hy1.symm),
    multiplyMonomial_pad _ _ (hx2.trans hy2.symm)]

theorem unitMonomial_pad (rank : Nat) : unitMonomial (rank+1) = pad (unitMonomial rank) := by
  unfold unitMonomial pad
  rw [List.replicate_add]
  rfl

theorem tensorPower_pad (rank degree : Nat) (p : List TensorMonomial)
    (hp : HomogeneousTensor rank degree p) (n : Nat) :
    tensorPower (rank+1) (p.map padTensor) n = (tensorPower rank p n).map padTensor := by
  induction n with
  | zero => simp [tensorPower,padTensor,unitMonomial_pad]
  | succ n ih =>
    rw [tensorPower,tensorPower,ih]
    apply tensorMultiply_pad rank
    · intro t ht
      exact ⟨(tensorPower_homogeneous rank degree p hp n t ht).1,
        (tensorPower_homogeneous rank degree p hp n t ht).2.1⟩
    · intro t ht
      exact ⟨(hp t ht).1,(hp t ht).2.1⟩

theorem fold_pad (rank : Nat) (f : Nat → List TensorMonomial) (degree : Nat → Nat)
    (indices : List Nat) (initial : List TensorMonomial) (d : Nat)
    (hi : HomogeneousTensor rank d initial)
    (hf : ∀ j ∈ indices, HomogeneousTensor rank (degree j) (f j)) :
    ((indices.map fun j => (f j).map padTensor).foldl tensorMultiply (initial.map padTensor)) =
      ((indices.map f).foldl tensorMultiply initial).map padTensor := by
  induction indices generalizing initial d with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [tensorMultiply_pad rank initial (f j)
      (fun t ht => ⟨(hi t ht).1,(hi t ht).2.1⟩)
      (fun t ht => ⟨(hf j (by simp) t ht).1,(hf j (by simp) t ht).2.1⟩)]
    apply ih _ (d+degree j)
    · exact tensorMultiply_homogeneous rank d (degree j) initial (f j) hi (hf j (by simp))
    · intro k hk
      exact hf k (by simp [hk])

theorem multiply_unit_right (m : Monomial) (rank : Nat) (hm : m.length = rank) :
    multiplyMonomial m (unitMonomial rank) = m := by
  subst rank
  induction m with
  | nil => rfl
  | cons a xs ih =>
    change (a+0) :: multiplyMonomial xs (unitMonomial xs.length) = a :: xs
    rw [ih,Nat.add_zero]

theorem tensor_unit_right (p : List TensorMonomial) (rank : Nat) (hp : TensorArity rank p) :
    tensorMultiply p [(unitMonomial rank,unitMonomial rank)] = p := by
  unfold tensorMultiply
  have he : ∀ t ∈ p, ([(unitMonomial rank,unitMonomial rank)].map fun y =>
      (multiplyMonomial t.1 y.1,multiplyMonomial t.2 y.2)) = [t] := by
    intro t ht
    simp only [List.map_cons,List.map_nil]
    rw [multiply_unit_right _ _ (hp t ht).1,multiply_unit_right _ _ (hp t ht).2]
  rw [List.flatMap_congr he]
  simp

theorem coproduct_pad (rank : Nat) (m : Monomial) (hm : m.length = rank) :
    coproduct (rank+1) (pad m) = (coproduct rank m).map padTensor := by
  let f := fun j => tensorPower rank (generatorCoproduct rank (j+1)) (m[j]?.getD 0)
  have hmaps : ((List.range rank).map fun j =>
      tensorPower (rank+1) (generatorCoproduct (rank+1) (j+1)) ((pad m)[j]?.getD 0)) =
      (List.range rank).map (fun j => (f j).map padTensor) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j < rank := List.mem_range.mp hj
    rw [generatorCoproduct_pad rank (j+1) (by omega)]
    have hget : (pad m)[j]? = m[j]? := List.getElem?_append_left (by omega)
    rw [hget,tensorPower_pad rank (2^(j+1)-1) _ (generatorCoproduct_homogeneous rank (j+1) (by omega))]
  unfold coproduct
  rw [List.range_succ,List.map_append,List.foldl_append]
  simp only [List.map_singleton,List.foldl_cons,List.foldl_nil]
  have hz : (pad m)[rank]?.getD 0 = 0 := by simp [pad,← hm]
  rw [hz,tensorPower,hmaps]
  have hu : [(unitMonomial (rank+1),unitMonomial (rank+1))] =
      [(unitMonomial rank,unitMonomial rank)].map padTensor := by simp [padTensor,unitMonomial_pad]
  rw [hu,fold_pad rank f (fun j => (m[j]?.getD 0)*(2^(j+1)-1)) (List.range rank) _ 0
    (tensorUnit_homogeneous rank) (fun j hj => tensorPower_homogeneous rank _ _
      (generatorCoproduct_homogeneous rank (j+1) (by have := List.mem_range.mp hj; omega)) _)]
  rw [← hu]
  change tensorMultiply ((coproduct rank m).map padTensor)
    [(unitMonomial (rank+1),unitMonomial (rank+1))] = (coproduct rank m).map padTensor
  apply tensor_unit_right _ (rank+1)
  intro t ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  have hh := coproduct_homogeneous rank m hm u hu
  simp [padTensor,pad,hh.1,hh.2.1]

theorem pad_injective : Function.Injective pad := by
  intro a b h
  exact List.append_cancel_right h

theorem coefficient_pad (p : Polynomial) (m : Monomial) :
    coefficient (p.map pad) (pad m) = coefficient p m := by
  unfold coefficient
  rw [List.filter_map]
  have he : (fun x => pad x == pad m) = (fun x => x == m) := by
    funext x
    simp only [beq_eq_decide, pad_injective.eq_iff]
  simp only [Function.comp_def,he,List.length_map]

theorem pairTensor_pad (left right : Polynomial) (terms : List TensorMonomial) :
    pairTensor (left.map pad) (right.map pad) (terms.map padTensor) = pairTensor left right terms := by
  unfold pairTensor
  rw [List.filter_map]
  have he : (fun t => coefficient (left.map pad) (padTensor t).1 &&
      coefficient (right.map pad) (padTensor t).2) =
      (fun t => coefficient left t.1 && coefficient right t.2) := by
    funext t
    simp only [padTensor,coefficient_pad]
  simp only [Function.comp_def,he,List.length_map]

/-- Coproduct pairing is unchanged by adjoining an unused generator, in all
degrees, provided the tested monomial is the zero-padded old monomial. -/
theorem product_pad (rank : Nat) (left right : Polynomial) (m : Monomial)
    (hm : m.length = rank) :
    pairTensor (left.map pad) (right.map pad) (coproduct (rank+1) (pad m)) =
      pairTensor left right (coproduct rank m) := by
  rw [coproduct_pad rank m hm,pairTensor_pad]

/-- If the new generator lies above the window, *every* monomial in that
higher-rank window is covered by the padding compatibility theorem. -/
theorem bounded_rank_stability (rank bound : Nat) (left right : Polynomial) (m : Monomial)
    (hm : m.length = rank+1) (hw : weight m ≤ bound) (henough : bound < 2^(rank+1)-1) :
    pairTensor (left.map pad) (right.map pad) (coproduct (rank+1) m) =
      pairTensor left right (coproduct rank (m.take rank)) := by
  have hp := bounded_succ_is_pad m rank bound hm hw henough
  conv_lhs => rw [hp]
  apply product_pad
  simp [hm]

def padMany : Nat → Monomial → Monomial
  | 0, m => m
  | n+1,m => pad (padMany n m)

theorem padMany_length (n : Nat) (m : Monomial) : (padMany n m).length = m.length+n := by
  induction n with
  | zero => simp [padMany]
  | succ n ih => simp [padMany,pad,ih,Nat.add_assoc]

/-- Any number of added zero coordinates leaves all product coefficients
unchanged; no bound on the tested monomial's degree is required. -/
theorem product_padMany (rank extra : Nat) (left right : Polynomial) (m : Monomial)
    (hm : m.length = rank) :
    pairTensor (left.map (padMany extra)) (right.map (padMany extra))
      (coproduct (rank+extra) (padMany extra m)) =
      pairTensor left right (coproduct rank m) := by
  induction extra with
  | zero => simp [padMany]
  | succ n ih =>
    have hl : left.map (padMany (n+1)) = (left.map (padMany n)).map pad := by
      simp [List.map_map,padMany,Function.comp_def]
    have hr : right.map (padMany (n+1)) = (right.map (padMany n)).map pad := by
      simp [List.map_map,padMany,Function.comp_def]
    rw [hl,hr,show rank+(n+1)=(rank+n)+1 by omega,padMany,
      product_pad (rank+n) _ _ _ (by simp [padMany_length,hm])]
    exact ih

#print axioms coproduct_pad
#print axioms bounded_rank_stability

/-- High-degree inputs to a coproduct also have high total tensor weight, so
low-degree homogeneous factors cannot see them, regardless of ambient rank. -/
theorem bounded_product_high_degree (rank d e : Nat) (left right : Polynomial)
    (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (m : Monomial) (hm : m.length = rank) (hw : d+e < weight m) :
    pairTensor left right (coproduct rank m) = false :=
  product_degree_support rank d e left right hl hr m hm (by omega)

#print axioms high_coordinate_zero
#print axioms coordinates_above_rank_zero

end MilnorCertificates
