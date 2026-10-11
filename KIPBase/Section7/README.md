# Section 7: proof of the main theorem

This directory is the workspace for reusable Lean results needed by Section 7
of the paper, `MainPaper/main.tex:2102–2782`. The goal of that section is the
permanent survival of `h₆²` in the classical Adams spectral sequence.

## Source and proof map

| Paper step | Paper label | Current project location |
| --- | --- | --- |
| Inductive criterion and the possible `d₁₂` | `thm:bjmbx`, `prop:possible_h_6_sq` | `KIP126/Main/Solution/DifferentialReduction/` |
| Choice independence for `θ₅` and the candidate extensions | `lem:equistate4`, `lem:equistate5` | `KIP126/Main/Solution/ChoiceIndependence/` |
| Toda bracket and two extension | `lem:toda2ext`, `cor:2ext125` | `KIP126/Main/Solution/Route/Section7.lean` |
| `ν` extension and cofiber obstruction | `lem:nuext125`, `prop:state5false` | `KIP126/Main/Solution/Route/Section7.lean`, `KIP126/Main/Solution/ExtensionObstruction/` |
| Permanent survival | `thm:126survives` | `KIP126/Main/Solution/h6_sq_permanent.lean` |

Place a result here when it is reusable without importing KIP126's fixed
model, computation package, or `Challenge2` witness. The Section 7 theorem,
its concrete near-126 data, and applications to the fixed sphere remain in
`KIP126/Main/Solution/`. Existing general tools are under
`KIPBase/Synthetic/`, `KIPBase/SpectralSequence/`, and
`KIPBase/multiplicativeSS/`; import those directly when needed.

The Blueprint's `near126.tex` and `coverage.tex` record the proof graph and
open obligations. A compiled module here does not by itself discharge those
obligations; each application must use the same model, grading, page
convention, and correlated inputs as the Section 7 proof.
