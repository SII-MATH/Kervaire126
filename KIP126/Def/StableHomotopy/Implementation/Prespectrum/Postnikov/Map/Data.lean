module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The unique induced map between the same constructed truncation objects,
chosen from their proved universal property. -/
noncomputable def sourcePostnikovMap (n : ℤ) {X Y : SourceCategory.{0}} (f : X ⟶ Y) :
    sourcePostnikovTruncation X n ⟶ sourcePostnikovTruncation Y n :=
  ((sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation Y n)
    (sourcePostnikovTruncation_homotopy_subsingleton Y n)).surjective
      (f ≫ sourcePostnikovUnit Y n)).choose

end KIP126.StableHomotopy.Implementation
