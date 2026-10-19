module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

/-- The original even level and the actual equal-index smash give the
same cubical loop space, using their proved equality of based spaces. -/
noncomputable def diagonalEvenLoopEquiv (X Y : Prespectrum.{0}) (n r : ℕ) :
    GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point ≃
    GenLoop (Fin r) ((X.level n).smash (Y.level n))
      ((X.level n).smash (Y.level n)).point :=
  Equiv.cast (congrArg (fun A : BasedSpace => ↥(GenLoop (Fin r) A A.point))
    (diagonalLevel_even X Y n))

end KIP126.StableHomotopy.Implementation.Prespectrum
