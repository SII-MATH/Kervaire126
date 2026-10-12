module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Loop.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

/-- The horizontal grid transition on original stable representatives.
The row degree increases by one, while the vertical spectrum stage stays fixed. -/
noncomputable def diagonalGridRowRepresentative (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ)
    (a : Representative (spaceSmash (X.level n) Y) (d+n)) :
    Representative (spaceSmash (X.level (n+1)) Y) (d+(n+1)) where
  stage := a.stage
  dimension := a.dimension+1
  degree := by have := a.degree; omega
  loop := diagonalGridLoopHorizontal X Y n a.stage a.dimension a.loop

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- The horizontal grid transition respects exactly the original
stable relation, including its vertical stabilization generator. -/
theorem diagonalGridRowRepresentative_relation (X Y : Prespectrum.{0}) (d : ℤ) (n : ℕ)
    {a b : Representative (spaceSmash (X.level n) Y) (d+n)}
    (h : StableRelation (spaceSmash (X.level n) Y) (d+n) a b) :
    (Quot.mk _ (diagonalGridRowRepresentative X Y d n a) :
      StableHomotopy (spaceSmash (X.level (n+1)) Y) (d+(n+1))) =
        Quot.mk _ (diagonalGridRowRepresentative X Y d n b) := by
  cases h with
  | homotopy p h =>
      exact Quot.sound (StableRelation.homotopy (diagonalGridRowRepresentative X Y d n a) _
        (diagonalGridLoopHorizontal_homotopic X Y n a.stage a.dimension a.loop p h))
  | stabilization =>
      exact (Quot.sound (StableRelation.stabilization
        (diagonalGridRowRepresentative X Y d n a))).trans
          (Quot.sound (StableRelation.homotopy (diagonalGridRowRepresentative X Y d n a).next _
            (diagonalGridLoop_interchange_homotopic X Y n a.stage a.dimension a.loop)))

end KIP126.StableHomotopy.Implementation.Prespectrum

end
