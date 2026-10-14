module

public import KIP126.LinProgram.Certificates.Secondary.Milnor.Products

@[expose] public section


namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- An exact ordered table for the ENTIRE homogeneous basis of the original rank.
The equality forbids missing or extra monomials and altered coproduct terms. -/
structure HomogeneousCoproductTable (rank degree : Nat) where
  table : List (Monomial × List TensorMonomial)
  complete : table = (degreeBasis rank degree).map (fun m => (m, fastCoproduct rank m))

/-- Reuse a separately certified full homogeneous coproduct table.
Arity and the actual input degree sum are still checked on every product. -/
def fastSingletonProductCheckWithTable {rank degree : Nat}
    (T : HomogeneousCoproductTable rank degree) (a b : Monomial)
    (output : Polynomial) : Bool :=
  a.length == rank && b.length == rank && weight a + weight b == degree &&
  output.all (fun m => m.length == rank && weight m == degree) &&
  T.table.all fun entry => coefficient output entry.1 == pairTensor [a] [b] entry.2

/-- A shared table certifies exactly the same original all-monomial product
predicate; neither its input nor its conclusion truncates rank or degree. -/
theorem fastSingletonProductCheckWithTable_sound {rank degree : Nat}
    (T : HomogeneousCoproductTable rank degree) (a b : Monomial) (output : Polynomial)
    (h : fastSingletonProductCheckWithTable T a b output = true) :
    IsMilnorProductAll rank [a] [b] output := by
  simp only [fastSingletonProductCheckWithTable, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hd⟩, ho⟩, hc⟩ := h
  apply fastSingletonProductCheck_sound rank a b output
  simp only [fastSingletonProductCheck, Bool.and_eq_true, beq_iff_eq, hd]
  refine ⟨⟨⟨ha, hb⟩, ho⟩, ?_⟩
  simpa only [T.complete, List.all_map, Function.comp_def] using hc

end KIP126.Computation.Secondary
