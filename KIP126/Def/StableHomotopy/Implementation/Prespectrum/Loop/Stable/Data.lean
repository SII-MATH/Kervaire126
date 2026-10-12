module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Cubical.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
universe u

/-- Uncurry an actual stable representative without changing its level. -/
def Representative.unloop {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (Prespectrum.loop X) d) : Representative X (d+1) where
  stage := a.stage
  dimension := a.dimension+1
  degree := by have := a.degree; omega
  loop := loopUncurryLast (X.level a.stage) a.dimension a.loop

/-- One stabilization supplies a last coordinate to curry, including
representatives whose original cubical dimension is zero. -/
def Representative.loopNext {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X (d+1)) : Representative (Prespectrum.loop X) d where
  stage := a.stage+1
  dimension := a.dimension
  degree := by have := a.degree; omega
  loop := loopCurryLast (X.level (a.stage+1)) a.dimension a.next.loop

end KIP126.StableHomotopy.Implementation.Prespectrum
