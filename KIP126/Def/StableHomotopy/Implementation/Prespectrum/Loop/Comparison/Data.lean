module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Stable.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

/-- Actual stable uncurrying, on the originally defined stable quotient. -/
def stableLoopHomotopyMap (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (Prespectrum.loop X) d → StableHomotopy X (d+1) :=
  Quot.map Representative.unloop (fun _ _ h => Representative.unloop_relation h)

/-- The cofinal inverse uses one stabilization before currying. -/
def stableLoopHomotopyInverse (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X (d+1) → StableHomotopy (Prespectrum.loop X) d :=
  Quot.map Representative.loopNext (fun _ _ h => Representative.loopNext_relation h)

end KIP126.StableHomotopy.Implementation.Prespectrum
