import KIP126.Interface.Challenge.Challenge2
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

namespace KIP126.Computation.LinProofs

/-- Compatibility name for the coordinate predicate frozen in Challenge 2. -/
def HasCoordinates {s t : Nat} (x : KIP126.LinE2.E2At s t)
    (indices : List Nat) : Prop :=
  KIP126.Challenge2.HasCoordinates x indices

/-- Meaning of one finite-page sphere record for the presentation selected by
the shared Challenge 2 witness. -/
noncomputable def DifferentialStatement (row : DifferentialRow) : Prop :=
  KIP126.Challenge2.DifferentialStatement
    KIP126.Classical.Adams.linE2Presentation row

end KIP126.Computation.LinProofs
