module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

/-- Every level of the actual fixed-space k-smash already has its
compactly generated quotient topology, regardless of its input levels. -/
instance spaceSmash_level_uCompactlyGeneratedSpace (A : BasedSpace.{0})
    (X : Prespectrum.{0}) (n : ℕ) : UCompactlyGeneratedSpace.{0} ((spaceSmash A X).level n) :=
  BasedSpace.smash_uCompactlyGeneratedSpace A (X.level n)

end KIP126.StableHomotopy.Implementation.Prespectrum
