module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Restriction.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- The actual Postnikov tower, using cutoffs 0, 1, 2, ... and the original
universal-property restrictions between the constructed truncation objects. -/
noncomputable def sourcePostnikovTower (X : SourceCategory.{0}) : InverseSequence SourceCategory.{0} where
  obj k := sourcePostnikovTruncation X (k : ℤ)
  step k := sourcePostnikovRestriction X (k+1 : ℕ) k (by omega)

end KIP126.StableHomotopy.Implementation
