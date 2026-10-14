module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- Restriction from a higher cutoff to a lower one, obtained from the
proved universal property of the same actual truncation objects. -/
noncomputable def sourcePostnikovRestriction (X : SourceCategory.{0}) (m n : ℤ) (h : n ≤ m) :
    sourcePostnikovTruncation X m ⟶ sourcePostnikovTruncation X n :=
  ((sourcePostnikovUnit_precomp_bijective X m (sourcePostnikovTruncation X n)
    (fun d hd => sourcePostnikovTruncation_homotopy_subsingleton X n d (h.trans hd))).surjective
      (sourcePostnikovUnit X n)).choose

end KIP126.StableHomotopy.Implementation
