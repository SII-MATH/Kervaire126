module

public import KIP126.LinProgram.Certificates.SquareDetection.Data
public import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

@[expose] public section

namespace KIP126.Classical.Adams

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- Compatibility form of the delivered nonzero-square conclusion. The finite
check is discharged by the Interface producer; Main consumes its C(M) field. -/
theorem computedH6Square_ne_zero_of_check
    (h : KIP126.LinE2.SquareDetection.allRelationsCheck = true) :
    computedH6Square ≠ 0 := by
  exact KIP126.Main.StageInput.witness.computation.results.sphereSquare.nonzero

/-- The fixed computational class is nonzero on E₂, as delivered by the
computation part of the one disclosed Challenge2 witness. -/
theorem computedH6Square_ne_zero : computedH6Square ≠ 0 :=
  KIP126.Main.StageInput.witness.computation.results.sphereSquare.nonzero

end KIP126.Classical.Adams
