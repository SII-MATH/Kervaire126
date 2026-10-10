# Lin program data and interpretation

The program pipeline imports pinned external computations. It does not construct
the standard sphere Adams sequence or establish the final survival theorem.

| Directory | Responsibility |
| --- | --- |
| `Raw/` | Archived CSV, database and log inputs, with the extraction manifest. |
| `Translate/` | Deterministic translation and fixed-input checks. |
| `Generated/` | Lean encodings of the imported records. |
| `Route/` | Selection of the fixed records used by the proof route. |
| `SourceMetadata/AppendixTable/` | Typed transcription of the paper tables, with row labels and locators; recorded statuses require mathematical justification. |
| `Model/E2/`, `Model/Classes/`, `Model/Product/` | The fixed truncated CSV quotient and its mathematical operations and elements. |
| `Model/BasisTable/`, `Certificates/BasisTable/` | Imported basis values and coordinates conditional on explicit basis certification. |
| `Compute/E2/`, `Tactic/Support/`, `Interpretation/Polynomial/`, `Interpretation/Expression/` | Parsing, reduction, expression interpretation and calculation support. |
| `Interpretation/` | Mathematical interpretation parameterized by a supplied model. |
| `Certificates/`, `Tactic/` | Local fixed-data certificates and calculation tactics. |

Generic E₂ table, page-algebra, presentation and input definitions belong to
`KIP126/Def/AdamsE2/`. The program-specific comparison with Def's fixed sphere
page is `KIP126/Interface/Challenge/Computation/Presentation.lean`.
`Interface/Challenge/Computation/Delivery.lean` specifies the correlated bindings
and results; `Interface/Solution/LinProgram/` constructs their certificates.
Main consumes those results from the same Challenge2 witness.

The quotient `KIP126.LinE2.E2` truncates internal degrees above 261. This is a
data algebra; its name does not identify it with the actual sphere E₂ page.
The bounded comparison, basis, actual multiplication, differential, staircase
and route conditions remain explicit mathematical obligations. In particular,
a staircase threshold alone does not prove nonzero permanent survival.

The relocation from `Def/AdamsE2/Lin*` preserves public declaration names and
proof status. The admitted `coordinateCheck_sound` and unfinished Interface
certifications remain unfinished. Successful import, hash checks, calculation
or compilation do not establish their mathematical correctness.

Source identities, locators, versions and hashes are recorded in the canonical
`docs/external-inputs.json` manifest; this README introduces no source registry
or additional assumptions.
