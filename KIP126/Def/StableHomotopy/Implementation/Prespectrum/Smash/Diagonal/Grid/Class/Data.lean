module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Loop.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

/-- An actual homotopy class at one two-index smash stage, retaining its
original cubical dimension and integer degree. -/
structure DiagonalGridClass (X Y : Prespectrum.{0}) (d : ℤ) where
  left : ℕ
  right : ℕ
  dimension : ℕ
  degree : (dimension : ℤ) = d+left+right
  homotopy : _root_.HomotopyGroup (Fin dimension)
    ((X.level left).smash (Y.level right)) ((X.level left).smash (Y.level right)).point

/-- The horizontal class transition is induced by the actual signed loop map. -/
noncomputable def DiagonalGridClass.horizontal {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) : DiagonalGridClass X Y d where
  left := a.left+1
  right := a.right
  dimension := a.dimension+1
  degree := by have := a.degree; omega
  homotopy := Quotient.map (diagonalGridLoopHorizontal X Y a.left a.right a.dimension)
    (diagonalGridLoopHorizontal_homotopic X Y a.left a.right a.dimension) a.homotopy

/-- The vertical class transition is the original spectrum stabilization. -/
noncomputable def DiagonalGridClass.vertical {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) : DiagonalGridClass X Y d where
  left := a.left
  right := a.right+1
  dimension := a.dimension+1
  degree := by have := a.degree; omega
  homotopy := stabilizeHomotopy (spaceSmash (X.level a.left) Y)
    a.right a.dimension a.homotopy

/-- Move an actual grid class from `(n,k)` to `(n+k,n+k)` using only
the two constructed transitions. This avoids any choice of a later stage. -/
noncomputable def DiagonalGridClass.normalize {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridClass X Y d) : DiagonalGridClass X Y d :=
  (DiagonalGridClass.horizontal^[a.right]) ((DiagonalGridClass.vertical^[a.left]) a)

end KIP126.StableHomotopy.Implementation.Prespectrum
