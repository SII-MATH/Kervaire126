import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data
import KIP126.Def.SpectralSequence.Permanence.Predicates

namespace KIP126.Classical.Adams

/-- Consume Interface's identification on the very same internal E₂ page.
The certificate and nonvanishing argument belong to the Interface producer;
this compatibility theorem only projects the one Challenge2 witness. -/
theorem computedH6Square_eq_standardH6Square : computedH6Square = standardH6Square :=
  KIP126.Main.StageInput.computation.results.sphereSquare.standard_class

/-- Rewriting T(M) using a computational label needs only
the equality of labels on M's sequence, not a change of spectral sequence. -/
theorem computedH6Square_nonzeroSurvival_iff_standard :
    KIP126.Core.SpectralSequence.NonzeroSurvival sphereAdamsData (2, 128) computedH6Square ↔
      KIP126.Core.SpectralSequence.NonzeroSurvival sphereAdamsData (2, 128) standardH6Square := by
  rw [computedH6Square_eq_standardH6Square]

end KIP126.Classical.Adams
