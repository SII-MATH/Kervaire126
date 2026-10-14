module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Separation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

/-- The actual spectrification telescope retains T₁ levels. -/
instance spectrificationTelescope_level_t1Space (X : Prespectrum.{u})
    [∀ n, T1Space (X.level n)] (n : ℕ) : T1Space ((spectrificationTelescope X).level n) := by
  letI (k n : ℕ) : T1Space (((spectrificationDiagram X).obj k).level n) :=
    inferInstanceAs (T1Space ((spectrificationStages X k).level n))
  exact sequentialColimit_level_t1Space (spectrificationDiagram X)
    (spectrificationDiagram_successor_closed X) n

end KIP126.StableHomotopy.Implementation.Prespectrum
