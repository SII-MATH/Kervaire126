module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Map.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Iterating the actual truncation functors with a smaller second cutoff
is naturally isomorphic to that smaller truncation. Its inverse is the
smaller truncation of the original larger-cutoff unit. -/
noncomputable def sourcePostnikovIterationIso (m n : ℤ) (h : n ≤ m) :
    sourcePostnikovFunctor m ⋙ sourcePostnikovFunctor n ≅ sourcePostnikovFunctor n := by
  exact (NatIso.ofComponents
    (fun (X : SourceCategory.{0}) => by
      letI := sourcePostnikovMap_unit_isIso X m n h
      exact asIso (sourcePostnikovMap n (sourcePostnikovUnit X m)))
    (fun f => by
      change sourcePostnikovMap n f ≫ sourcePostnikovMap n (sourcePostnikovUnit _ m) =
        sourcePostnikovMap n (sourcePostnikovUnit _ m) ≫
          sourcePostnikovMap n (sourcePostnikovMap m f)
      rw [← sourcePostnikovMap_comp, ← sourcePostnikovMap_comp,
        sourcePostnikovUnit_naturality])).symm

end KIP126.StableHomotopy.Implementation
