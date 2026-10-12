module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Tail.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Bond.Existence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

noncomputable def pairedBond (X Y : Prespectrum.{0}) :
    C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) := (pairedBond_exists X Y).exists.choose

def diagonalLevel (X Y : Prespectrum.{0}) : ℕ → BasedSpace.{0}
  | 0 => (X.level 0).smash (Y.level 0)
  | 1 => ((X.level 0).smash (Y.level 0)).suspension
  | n+2 => diagonalLevel X.tail Y.tail n

noncomputable def diagonalBond (X Y : Prespectrum.{0}) :
    ∀ n, C(diagonalLevel X Y n × I, diagonalLevel X Y (n+1))
  | 0 => BasedSpace.suspensionProjection _
  | 1 => pairedBond X Y
  | n+2 => diagonalBond X.tail Y.tail n

end Prespectrum
end KIP126.StableHomotopy.Implementation
