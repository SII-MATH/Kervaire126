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
| `Model/BasisCatalogue/`, `Certificates/BasisCertification/` | Imported basis values and coordinates conditional on explicit basis certification. |
| `Compute/E2/`, `Tactic/Support/`, `Interpretation/Polynomial/`, `Interpretation/Expression/` | Parsing, reduction, expression interpretation and calculation support. |
| `Interpretation/` | Mathematical interpretation parameterized by a supplied model. |
| `Certificates/Verifier.lean`, `Tactic/LinCert.lean` | Certificate contracts and the generic `lin_cert` tactic. |
| `Certificates/NamedElements/` | Polynomial and module-expression checkers and their evaluation soundness proofs. |
| `Certificates/Milnor/` | Executable Milnor calculations, grading and rank bounds, and their soundness proofs. |
| Other `Certificates/` and `Tactic/` modules | Local fixed-data certificates and project calculation tactics. |

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

## Independence from the research attempt

The top-level `Lin-program/` remains an independent research project. KIP126
owns the certificate modules it uses; its build does not import modules or
take source roots from that directory. The adopted modules are ordinary parts
of the existing `KIP126` Lake library, with no additional shared package.

The initial adoption copies the complete 20-module dependency closure of the
three certificate libraries used at commit
`0cacf987437cfeff3f5c067a7a025182648516e0`. The source paths below are relative
to `Lin-program/program/`; the destination paths are relative to this directory.

| Research source | KIP126-owned location | Responsibility |
| --- | --- | --- |
| `LinProgramCertificates/Verifier.lean` | `Certificates/Verifier.lean` | Bind a certificate type, executable check and soundness theorem to a proposition. |
| `LinProgramCertificates/Tactic.lean` | `Tactic/LinCert.lean` | Apply the checked soundness theorem through `lin_cert`. |
| `NamedElementCertificates/{Basic,Evaluation,ModuleEvaluation}.lean` | `Certificates/NamedElements/` | Verify relation witnesses and interpret the resulting polynomial or module equalities. |
| The 15 selected `MilnorCertificates/` modules | `Certificates/Milnor/` | Certify the finite Milnor computations used by the secondary calculation support. |

Only import paths and one inherited trailing space change during adoption.
Public declaration names, including
`LinProgramCertificates`, `NamedElementCertificates` and `MilnorCertificates`
namespaces, are retained; they do not denote a dependency on the old project.
The original source tree is unchanged. Later changes in that tree do not
automatically change the KIP126 copies.

Some data-reconstruction scripts still locate the archived input under
`Lin-program/program/upstream/`. This adoption removes the Lean source
dependency; input locations and historical provenance records are unchanged.

These support modules depend only on Lean, Mathlib and one another. Concrete
inputs and certificates remain in the other LinProgram modules; comparison
with the fixed mathematical objects remains in Interface. Moving the support
code does not construct the bounded presentation or prove an actual Adams
differential. Historical audit paths and proof-completion statuses are retained.

## Finding a theorem by subject

The file path gives its subject and role. Public declaration names are retained
across file moves, so a namespace such as `KIP126.LinE2.OneLine` is a stable API
name, not a second file location. Import the concrete module below; there are no
one-module compatibility wrappers at the old paths.

| Subject | Data certificates | Fixed-model Interface |
| --- | --- | --- |
| Recorded basis versus certified basis | `Model/BasisCatalogue/Data.lean`; `Certificates/BasisCertification/{Predicates,Data,Proofs}.lean` | `Basis/Certification.lean` states the unfinished catalogue-correctness obligation; `Basis/Comparison.lean` transports it through the supplied comparison. |
| One-line d₂ row 5434, h₄ to h₀h₃² | `Certificates/AdamsOneLine/H4Source.lean`, `H4Target.lean` | `AdamsOneLine/H4.lean` |
| One-line d₂ row 5541, h₆ to h₀h₅² | `Certificates/AdamsOneLine/H6Coordinates.lean` | `AdamsOneLine/H6.lean` |
| Hopf class h₁ and η | `Certificates/Hopf/H1Coordinates.lean` | `Hopf/H1Comparison.lean` |
| Vanishing-target d₂ row 5432 | `Certificates/Differentials/Row5432Coordinates.lean` | `Differentials/VanishingD2.lean` |
| Trial 152097 products | `Certificates/Products/Trial152097.lean`, `Trial152097Coordinates.lean` | `Products/Trial152097.lean` |
| Naturality row 245131 | `Certificates/Naturality/Row245131Coordinates.lean` | `Naturality/Row245131Coordinates.lean`, `Row245131.lean` |
| Naturality row 462481 | `Certificates/Naturality/Row462481Coordinates.lean`; `Certificates/Products/Naturality462481.lean`, `Naturality462481Modules.lean` | `Naturality/Row462481.lean`; `Naturality/CWModel.lean`, `CWToCeta.lean` construct the same CW-to-Cη conditional chain. |

Interface paths in this table are relative to
`KIP126/Interface/Solution/LinProgram/`. The paths do not indicate that an
actual-model comparison or a recorded differential has been certified.

## Shared exhaustion proof

[Def/Algebra/TwoElement/Proofs.lean](../Def/Algebra/TwoElement/Proofs.lean)
proves that a vector in an F₂ singleton span is zero or the specified spanning
vector. It also proves, over every semiring, that a linear equivalence transports
that exhaustion and identifies any independently specified nonzero vector.
[Model/E2/Proofs.lean](Model/E2/Proofs.lean) specializes the span lemma to the
existing homogeneous data component. The h₁, h₄, h₀h₃², h₆, h₀h₅² and h₆² data and
Interface proofs reuse these lemmas; each case still proves its own full-degree
exhaustion and retains the same nonvanishing and literature inputs.

## Module path migration

The following table records file locations only. Names inside Lean declarations,
Blueprint labels, mathematical statements, input bytes and proof status are
preserved. Historical audit snapshots retain the file paths recorded when they
were produced, including the `module` locators in `row462481-trace.json`; use this
table to locate their declarations today. Archived hash reports and immutable
trace snapshots are not rewritten to pretend that a historical file had a new
path. Executable Lean imports and current replay commands use the new paths.

| Former module path | Current module path |
| --- | --- |
| `KIP126/LinProgram/Model/BasisTable/Data.lean` | `KIP126/LinProgram/Model/BasisCatalogue/Data.lean` |
| `KIP126/LinProgram/Certificates/BasisTable/Data.lean` | `KIP126/LinProgram/Certificates/BasisCertification/Data.lean` |
| `KIP126/LinProgram/Certificates/BasisTable/Predicates.lean` | `KIP126/LinProgram/Certificates/BasisCertification/Predicates.lean` |
| `KIP126/LinProgram/Certificates/BasisTable/Proofs.lean` | `KIP126/LinProgram/Certificates/BasisCertification/Proofs.lean` |
| `KIP126/Interface/Solution/LinProgram/BasisTable.lean` | `KIP126/Interface/Solution/LinProgram/Basis/Certification.lean` |
| `KIP126/Interface/Solution/LinProgram/SphereBasis.lean` | `KIP126/Interface/Solution/LinProgram/Basis/Comparison.lean` |
| `KIP126/LinProgram/Certificates/OneLine.lean` | `KIP126/LinProgram/Certificates/AdamsOneLine/H4Source.lean` |
| `KIP126/LinProgram/Certificates/OneLineTarget.lean` | `KIP126/LinProgram/Certificates/AdamsOneLine/H4Target.lean` |
| `KIP126/LinProgram/Certificates/OneLineH6.lean` | `KIP126/LinProgram/Certificates/AdamsOneLine/H6Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/OneLine.lean` | `KIP126/Interface/Solution/LinProgram/AdamsOneLine/H4.lean` |
| `KIP126/Interface/Solution/LinProgram/OneLineH6.lean` | `KIP126/Interface/Solution/LinProgram/AdamsOneLine/H6.lean` |
| `KIP126/LinProgram/Certificates/H1.lean` | `KIP126/LinProgram/Certificates/Hopf/H1Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/H1.lean` | `KIP126/Interface/Solution/LinProgram/Hopf/H1Comparison.lean` |
| `KIP126/LinProgram/Certificates/LowStem.lean` | `KIP126/LinProgram/Certificates/Differentials/Row5432Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/Differentials.lean` | `KIP126/Interface/Solution/LinProgram/Differentials/VanishingD2.lean` |
| `KIP126/LinProgram/Certificates/ReplayProducts.lean` | `KIP126/LinProgram/Certificates/Products/Trial152097.lean` |
| `KIP126/LinProgram/Certificates/ReplayCoordinates.lean` | `KIP126/LinProgram/Certificates/Products/Trial152097Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/ReplayProducts.lean` | `KIP126/Interface/Solution/LinProgram/Products/Trial152097.lean` |
| `KIP126/LinProgram/Certificates/NaturalityHighStemProducts.lean` | `KIP126/LinProgram/Certificates/Products/Naturality462481.lean` |
| `KIP126/LinProgram/Certificates/NaturalityModuleProducts.lean` | `KIP126/LinProgram/Certificates/Products/Naturality462481Modules.lean` |
| `KIP126/LinProgram/Certificates/NaturalityCoordinates.lean` | `KIP126/LinProgram/Certificates/Naturality/Row245131Coordinates.lean` |
| `KIP126/LinProgram/Certificates/NaturalityHighStemCoordinates.lean` | `KIP126/LinProgram/Certificates/Naturality/Row462481Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/Naturality.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/Row245131.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityCoordinates.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/Row245131Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityHighStem.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/Row462481.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityCW.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/CWToCeta.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityCW/Model.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/CWModel.lean` |
