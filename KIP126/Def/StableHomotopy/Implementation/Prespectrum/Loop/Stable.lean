module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Cubical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

theorem Representative.unloop_next {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (Prespectrum.loop X) d) : a.next.unloop = a.unloop.next := by
  rfl

theorem Representative.loopNext_next {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X (d+1)) : a.next.loopNext = a.loopNext.next := by
  cases a with | mk n r hd p =>
    change Representative.mk _ _ _ _ = Representative.mk _ _ _ _
    congr 1
    exact loopCurryLast_stabilize X (n+1) r (stabilizeLoop X n r p)

@[simp] theorem Representative.unloop_loopNext {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X (d+1)) : a.loopNext.unloop = a.next := by
  cases a with | mk n r hd p =>
    change Representative.mk _ _ _ _ = Representative.mk _ _ _ _
    congr 1
    exact loopUncurryLast_loopCurryLast (X.level (n+1)) r (stabilizeLoop X n r p)

@[simp] theorem Representative.loopNext_unloop {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (Prespectrum.loop X) d) : a.unloop.loopNext = a.next := by
  cases a with | mk n r hd p =>
    change Representative.mk _ _ _ _ = Representative.mk _ _ _ _
    congr 1
    change loopCurryLast (X.level (n+1)) (r+1)
      (stabilizeLoop X n (r+1) (loopUncurryLast (X.level n) r p)) =
        stabilizeLoop (Prespectrum.loop X) n r p
    rw [loopCurryLast_stabilize,loopCurryLast_loopUncurryLast]

theorem Representative.unloop_relation {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative (Prespectrum.loop X) d} (h : StableRelation (Prespectrum.loop X) d a b) :
    StableRelation X (d+1) a.unloop b.unloop := by
  cases h with
  | homotopy p h =>
    exact StableRelation.homotopy _ _ ((loopUncurryLast_homotopic_iff _ _ _ _).mpr h)
  | stabilization =>
    rw [Representative.unloop_next]
    exact StableRelation.stabilization _

theorem Representative.loopNext_relation {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative X (d+1)} (h : StableRelation X (d+1) a b) :
    StableRelation (Prespectrum.loop X) d a.loopNext b.loopNext := by
  cases h with
  | homotopy p h =>
    exact StableRelation.homotopy _ _ (loopCurryLast_homotopic _ _
      (stabilizeLoop_homotopic X _ _ _ _ h))
  | stabilization =>
    rw [Representative.loopNext_next]
    exact StableRelation.stabilization _

end KIP126.StableHomotopy.Implementation.Prespectrum

end
