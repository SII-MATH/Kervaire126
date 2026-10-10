import KIP126.LinProgram.Generated.Staircase.Table
import KIP126.LinProgram.Interpretation.State.Data
open KIP126.Computation.LinProofs
#eval do
  let mut counts : Array Nat := #[0, 0, 0, 0]
  let mut total := 0
  for shard in [:StaircaseData.shardCount] do
    for offset in [:128] do
      if let some row := StaircaseData.lookup shard offset then
        total := total + 1
        let some claim := State.decode row
          | throw (IO.userError s!"row {row.id} failed to decode")
        let bucket := match claim with
          | .equation .. => 0
          | .reaches 1000 .. => 1
          | .reaches .. => 2
          | .boundaryBy .. => 3
        counts := counts.modify bucket (· + 1)
  unless total == 23822 && counts == #[15786, 1621, 6279, 136] do
    throw (IO.userError s!"unexpected coverage: {total}, {counts}")
  IO.println s!"PASS actual Lean decoder: {total} rows; {counts}"
-- Executable syntax regressions; these are not mathematical soundness proofs.
#eval do
  let cases : List (Raw.StaircaseRow × Option State.Claim) := [
    (⟨0, some 0, some 0, some "0", some "", some 9000⟩,
      some (.reaches 1000 0 0 [0])),
    (⟨1, some 5, some 20, some "0", none, some 3⟩,
      some (.boundaryBy 3 5 20 [0])),
    (⟨1, some 5, some 20, some "0", some "1", some 3⟩,
      some (.equation 3 2 18 [1] [0])),
    (⟨1, some 1, some 260, some "0", some "1", some 9997⟩, none)]
  for (row, expected) in cases do
    unless State.decode row == expected do
      throw (IO.userError s!"wrong row interpretation: {reprStr row}")
  for text in ["1,1", "2,1", "-1", "[NULL]"] do
    unless State.parseCoordinates text == none do
      throw (IO.userError s!"invalid coordinates accepted: {text}")
  IO.println "PASS syntax: threshold, boundary bound, inverse degree, range, unknowns"
