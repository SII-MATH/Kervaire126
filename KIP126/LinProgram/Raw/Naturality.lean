module

public import KIP126.LinProgram.Raw.Data
public import KIP126.LinProgram.Generated.Differentials.Shard051

@[expose] public section


/-!
# One fixed native naturality target and its adjacent source candidate

These are lossless rows of the pinned log. The `N` tag and adjacent `D`
row do not prove either equation or that the latter is the full trace.
The selected `Ceta__S0` map is `top_cell` with `sus = 2` in `ss.json`.
It preserves filtration and lowers the displayed internal degree by two.
-/

namespace KIP126.Computation.LinProofs.Raw.Naturality

def sourceCandidate245130 : LogRow where
  id := 245130
  depth := some 0
  reason := some "D"
  name := some "Ceta"
  stem := some 17
  s := some 2
  t := some 19
  r := some 3
  x := some "0"
  dx := some "0"
  info := none

def target245131 : LogRow where
  id := 245131
  depth := some 0
  reason := some "N"
  name := some "S0"
  stem := some 15
  s := some 2
  t := some 17
  r := some 3
  x := some "0"
  dx := some "0"
  info := some "Ceta__S0"

/-- The normalized native sphere output, without a paper class name. -/
def output245131 : DifferentialRow := ⟨245131, "N", 2, 17, 3, [0], [0]⟩

set_option maxRecDepth 4096 in
/-- The target is already present in the fixed conservative export. This
checks a transcription; it supplies no spectral-sequence proposition. -/
theorem output245131_in_export :
    RawData.shard51[43]? = some output245131 := rfl

/-- The native map's suspension shift, not a degree-preserving E₂ map. -/
def mapSuspension : Int := 2

theorem native_source_degree_shift :
    sourceCandidate245130.s = target245131.s ∧
      sourceCandidate245130.t.map (· - mapSuspension) = target245131.t := by
  decide

end KIP126.Computation.LinProofs.Raw.Naturality
