module

public import KIP126.LinProgram.Certificates.Secondary.Milnor.Degree
public import KIP126.LinProgram.Certificates.Secondary.Milnor.TensorCoefficient
public import KIP126.LinProgram.Certificates.Secondary.Milnor.FastCoproduct

@[expose] public section


namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- The fast coproduct gives exactly the original singleton-pair coefficient,
for every monomial of the original rank. -/
theorem pairTensor_fastCoproduct_singletons (rank : Nat) (a b m : Monomial)
    (ha : a.length = rank) (hb : b.length = rank) (hm : m.length = rank) :
    pairTensor [a] [b] (fastCoproduct rank m) = pairTensor [a] [b] (coproduct rank m) := by
  apply pairTensor_singletons_of_universal_eq rank a b ha hb
  · exact fastCoproduct_arity rank m
  · intro t ht
    have hh := coproduct_homogeneous rank m hm t ht
    exact ⟨hh.1, hh.2.1⟩
  · exact fastCoproduct_value (universalVariable 0) (universalVariable 1) rank m

/-- Exhaust the exact homogeneous degree with the original rank retained.
All coefficients use the accelerated coproduct with proved original semantics. -/
def fastSingletonProductCheck (rank : Nat) (a b : Monomial) (output : Polynomial) : Bool :=
  a.length == rank && b.length == rank &&
  output.all (fun m => m.length == rank && weight m == weight a + weight b) &&
  (degreeBasis rank (weight a + weight b)).all fun m =>
    coefficient output m == pairTensor [a] [b] (fastCoproduct rank m)

/-- A successful finite check proves the original product predicate on EVERY
monomial of the original rank, including all degrees outside the enumerated degree. -/
theorem fastSingletonProductCheck_sound (rank : Nat) (a b : Monomial) (output : Polynomial)
    (h : fastSingletonProductCheck rank a b output = true) :
    IsMilnorProductAll rank [a] [b] output := by
  simp only [fastSingletonProductCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, ho⟩, hc⟩ := h
  apply homogeneousProductCheck_sound rank (weight a) (weight b) [a] [b] output
  simp only [homogeneousProductCheck, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ho⟩, ?_⟩
  · simp [ha]
  · simp [hb]
  · apply List.all_eq_true.mpr
    intro m hm
    have hh := (List.all_eq_true.mp hc) m hm
    rw [pairTensor_fastCoproduct_singletons rank a b m ha hb
      ((degreeBasis_mem rank _ m).mp hm).1] at hh
    exact hh

end KIP126.Computation.Secondary
