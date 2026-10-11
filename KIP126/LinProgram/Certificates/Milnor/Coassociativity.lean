module

public import KIP126.LinProgram.Certificates.Milnor.RankStability

@[expose] public section


namespace MilnorCertificates

abbrev TripleMonomial := Monomial × Monomial × Monomial

/-- (Delta tensor identity) Delta, using the actual executable coproduct. -/
def coproductLeft (rank : Nat) (m : Monomial) : List TripleMonomial :=
  (coproduct rank m).flatMap fun t =>
    (coproduct rank t.1).map fun u => (u.1,u.2,t.2)

/-- (identity tensor Delta) Delta. -/
def coproductRight (rank : Nat) (m : Monomial) : List TripleMonomial :=
  (coproduct rank m).flatMap fun t =>
    (coproduct rank t.2).map fun u => (t.1,u.1,u.2)

def tripleCoefficient (p : List TripleMonomial) (t : TripleMonomial) : Bool :=
  (p.filter (· == t)).length % 2 == 1

def CoassociativeAt (rank : Nat) (m : Monomial) : Prop :=
  ∀ t, tripleCoefficient (coproductLeft rank m) t = tripleCoefficient (coproductRight rank m) t

/-- Finite support suffices to compare all coefficients, even outside the
enumerated triples. No coassociativity assumption is used. -/
def checkCoassociative (rank : Nat) (m : Monomial) : Bool :=
  (coproductLeft rank m ++ coproductRight rank m).all fun t =>
    tripleCoefficient (coproductLeft rank m) t == tripleCoefficient (coproductRight rank m) t

theorem tripleCoefficient_absent (p : List TripleMonomial) (t : TripleMonomial) (h : t ∉ p) :
    tripleCoefficient p t = false := by
  have he : p.filter (· == t) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [beq_iff_eq]
    intro hxt
    exact h (hxt ▸ hx)
  simp [tripleCoefficient,he]

theorem checkCoassociative_sound (rank : Nat) (m : Monomial)
    (h : checkCoassociative rank m = true) : CoassociativeAt rank m := by
  intro t
  by_cases ht : t ∈ coproductLeft rank m ++ coproductRight rank m
  · exact beq_iff_eq.mp (List.all_eq_true.mp h t ht)
  · simp only [List.mem_append,not_or] at ht
    rw [tripleCoefficient_absent _ _ ht.1,tripleCoefficient_absent _ _ ht.2]

def padTriple (t : TripleMonomial) : TripleMonomial := (pad t.1,pad t.2.1,pad t.2.2)

theorem coproductLeft_pad (rank : Nat) (m : Monomial) (hm : m.length = rank) :
    coproductLeft (rank+1) (pad m) = (coproductLeft rank m).map padTriple := by
  unfold coproductLeft
  rw [coproduct_pad rank m hm]
  simp only [List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro t ht
  have hh := (coproduct_homogeneous rank m hm t ht).1
  change (coproduct (rank+1) (pad t.1)).map (fun u => (u.1,u.2,pad t.2)) = _
  rw [coproduct_pad rank t.1 hh]
  simp only [List.map_map,Function.comp_def,padTensor,padTriple]

theorem coproductRight_pad (rank : Nat) (m : Monomial) (hm : m.length = rank) :
    coproductRight (rank+1) (pad m) = (coproductRight rank m).map padTriple := by
  unfold coproductRight
  rw [coproduct_pad rank m hm]
  simp only [List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro t ht
  have hh := (coproduct_homogeneous rank m hm t ht).2.1
  change (coproduct (rank+1) (pad t.2)).map (fun u => (pad t.1,u.1,u.2)) = _
  rw [coproduct_pad rank t.2 hh]
  simp only [List.map_map,Function.comp_def,padTensor,padTriple]

theorem padTriple_injective : Function.Injective padTriple := by
  intro a b h
  have h1 := congrArg (fun t : TripleMonomial => t.1) h
  have h2 := congrArg (fun t : TripleMonomial => t.2.1) h
  have h3 := congrArg (fun t : TripleMonomial => t.2.2) h
  exact Prod.ext (pad_injective h1) (Prod.ext (pad_injective h2) (pad_injective h3))

theorem tripleCoefficient_pad (p : List TripleMonomial) (t : TripleMonomial) :
    tripleCoefficient (p.map padTriple) (padTriple t) = tripleCoefficient p t := by
  unfold tripleCoefficient
  rw [List.filter_map]
  have he : (fun x => padTriple x == padTriple t) = (fun x => x == t) := by
    funext x
    simp only [beq_eq_decide,padTriple_injective.eq_iff]
  simp only [Function.comp_def,he,List.length_map]

theorem coassociative_pad (rank : Nat) (m : Monomial) (hm : m.length = rank)
    (h : CoassociativeAt rank m) : CoassociativeAt (rank+1) (pad m) := by
  intro t
  rw [coproductLeft_pad rank m hm,coproductRight_pad rank m hm]
  by_cases ht : ∃ u, padTriple u = t
  · obtain ⟨u,rfl⟩ := ht
    rw [tripleCoefficient_pad,tripleCoefficient_pad]
    exact h u
  · have hn (p : List TripleMonomial) : t ∉ p.map padTriple := by
      intro hh
      obtain ⟨u,hu,he⟩ := List.mem_map.mp hh
      exact ht ⟨u,he⟩
    rw [tripleCoefficient_absent _ _ (hn _),tripleCoefficient_absent _ _ (hn _)]

/-- Actual generator computations xi_1, xi_2, xi_3; the conclusion quantifies
every triple monomial, not only those listed in the computation. -/
theorem generators_rank_three (k : Nat) (hk : k ≤ 3) :
    CoassociativeAt 3 (generatorPower 3 k 1) := by
  have h : ∀ k ∈ List.range 4, checkCoassociative 3 (generatorPower 3 k 1) = true := by decide
  apply checkCoassociative_sound
  exact h k (List.mem_range.mpr (by omega))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem monomials_rank_two_degree_four (m : Monomial) (hm : m.length = 2) (hw : weight m ≤ 4) :
    CoassociativeAt 2 m := by
  have h : ∀ m ∈ basis 2 4, checkCoassociative 2 m = true := by decide
  exact checkCoassociative_sound 2 m (h m (basis_complete 2 4 m hm hw))

#print axioms checkCoassociative_sound
#print axioms generators_rank_three
#print axioms monomials_rank_two_degree_four

end MilnorCertificates
