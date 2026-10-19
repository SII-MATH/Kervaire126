module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Abelian.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

/-- The original cubical loop-degree equivalence as an additive equivalence. -/
def stableLoopHomotopyAddEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (Prespectrum.loop X) d ≃+ StableHomotopy X (d+1) where
  toEquiv := stableLoopHomotopyEquiv X d
  map_add' := stableLoopHomotopyMap_add X d

end KIP126.StableHomotopy.Implementation.Prespectrum
