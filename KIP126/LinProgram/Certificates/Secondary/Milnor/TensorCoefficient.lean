import KIP126.LinProgram.Certificates.Milnor.PolynomialExtraction

namespace KIP126.Computation.Secondary
open MilnorCertificates

private def asTriple (t : TensorMonomial) : TripleMonomial := (t.1,t.2,[])

private theorem tripleValue_asTriple {R : Type*} [CommRing R] [CharP R 2]
    (x y z : Nat → R) (p : List TensorMonomial) :
    tripleValue x y z (p.map asTriple) = tensorValue x y p := by
  simp only [tripleValue, tensorValue, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp [asTriple, monomialValue]

private theorem singleton_pair (a b : Monomial) (p : List TensorMonomial) :
    pairTensor [a] [b] p = ((p.filter (· == (a,b))).length % 2 == 1) := by
  have hp (t : TensorMonomial) :
      (coefficient [a] t.1 && coefficient [b] t.2) = (t == (a,b)) := by
    rcases t with ⟨x,y⟩
    by_cases ha : a = x <;> by_cases hb : b = y <;>
      simp_all [coefficient, Prod.ext_iff] <;> aesop
  simp only [pairTensor, hp]

private theorem triple_count (a b : Monomial) (p : List TensorMonomial) :
    ((p.map asTriple).filter (· == (a,b,[]))).length =
      (p.filter (· == (a,b))).length := by
  rw [List.filter_map, List.length_map]
  congr 2
  funext t
  simp [asTriple, Prod.ext_iff]

/-- Equality in the existing universal polynomial interpretation reflects
back to the original executable singleton-pair coefficient, for every pair
of monomials of the same rank. -/
theorem pairTensor_singletons_of_universal_eq
    (rank : Nat) (a b : Monomial) (ha : a.length = rank) (hb : b.length = rank)
    (p q : List TensorMonomial)
    (hp : ∀ t ∈ p, t.1.length = rank ∧ t.2.length = rank)
    (hq : ∀ t ∈ q, t.1.length = rank ∧ t.2.length = rank)
    (h : tensorValue (universalVariable 0) (universalVariable 1) p =
      tensorValue (universalVariable 0) (universalVariable 1) q) :
    pairTensor [a] [b] p = pairTensor [a] [b] q := by
  have hps : ∀ u ∈ p.map asTriple,
      u.1.length = a.length ∧ u.2.1.length = b.length ∧ u.2.2.length = ([] : Monomial).length := by
    intro u hu
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
    exact ⟨(hp t ht).1.trans ha.symm, (hp t ht).2.trans hb.symm, rfl⟩
  have hqs : ∀ u ∈ q.map asTriple,
      u.1.length = a.length ∧ u.2.1.length = b.length ∧ u.2.2.length = ([] : Monomial).length := by
    intro u hu
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
    exact ⟨(hq t ht).1.trans ha.symm, (hq t ht).2.trans hb.symm, rfl⟩
  rw [← tripleValue_asTriple _ _ (universalVariable 2) p,
      ← tripleValue_asTriple _ _ (universalVariable 2) q] at h
  have hc := congrArg (MvPolynomial.coeff (tripleEncoding (a,b,[]))) h
  rw [universalTriple_coefficient _ (a,b,[]) hps,
      universalTriple_coefficient _ (a,b,[]) hqs] at hc
  have hm := congrArg ZMod.val hc
  simp only [ZMod.val_natCast, triple_count] at hm
  rw [singleton_pair, singleton_pair, hm]

end KIP126.Computation.Secondary
