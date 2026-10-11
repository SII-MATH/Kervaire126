# Kervaire126 agent guidance

## Start here

- The Blueprint is the mathematical plan, not evidence that a proof is complete.
- Blueprint nodes describe mathematical objects, statements, and proof
  dependencies.
- A mechanical cleanup must not silently change a public declaration, a
  stage-boundary statement, source provenance, proof status, or mathematical
  strength.

## KIP126 Blueprint synchronization

For a Lean code task under `KIP126/`, read the relevant Blueprint chapter and
its dependency nodes before editing. Keep `blueprint/src/content.tex` and the
chapter files synchronized with the Lean code:

- update the linked declaration when a public statement, proof stage, source
  premise, or mathematical dependency changes;
- keep `\lean`, `\uses`, `\leanok`, and `\notready` consistent with the actual
  declaration and its proof dependencies;
- preserve stable Blueprint labels and public Lean names unless an API change is
  explicitly required;
- run `leanblueprint web`, the active-label/dependency check, and the relevant
  source/interface checks before completing the task.

Blueprint synchronization records the mathematical plan and proof status; it
does not turn compilation, generated output, or input certification into a
completed proof.

## Repository architecture

The extraction boundary recorded on `main` also applies to `develop`.
Do not restore the removed `KIPBase/` component, historical `docs/archive/`,
`docs/audits/`, or `docs/migration/` trees, Euler/Multica configuration,
or the old CI, review, merge, status, cache, performance, and publishing tools.
When integrating old work, retain concrete KIP126 and Blueprint changes while
preserving this boundary and the current main CI. Keep existing source attribution.

- `KIP126/Def/` owns common mathematical objects, predicates, constructions,
  the fixed implementation, route and mathematical background, its fixed-sphere
  applicability statement, and reusable theorems. Generic mathematical interfaces
  belong here, grouped by subject. It must not declare project axioms or import
  `LinProgram/`, `Interface/`, or `Main/`.
- `KIP126/Interface/` constructs one `Challenge2` witness. It owns
  literature source bindings and results, fixed-computation bindings and
  certification, and the resulting delivery interfaces on Def's fixed model.
- `KIP126/Main/` consumes Challenge2 and proves the paper's intermediate and
  final results. Intermediate statements and proofs belong in `Main/Solution/`;
  only the final target has a Main Challenge/Solution pair.
- `KIP126/LinProgram/` owns pinned program artifacts, deterministic
  translation, generated Lean data, parameterized interpretation, and local
  certificates. Data models, computations, and interpretation support tied to
  these artifacts belong here, rather than in Def. The fixed sphere comparison
  belongs to `Interface/Challenge/Computation/Presentation.lean`; LinProgram must
  not depend on Def's fixed stage model. These artifacts do not by themselves prove that the data model
  the selected mathematical object.
  Its `SourceMetadata/` subdirectory owns the typed transcription of the paper's appendix
  tables, including row labels, locators, and recorded statuses. It is independent
  of the mathematical deliveries and does not replace `docs/external-inputs.json`.
  A recorded status is not a proved differential or survival statement.
- `MainPaper/` owns the paper being formalized. `Source/` owns external
  literature artifacts, acquisition metadata, and the machine-readable source
  artifacts. The canonical source and input manifest is `docs/external-inputs.json`.
  These are provenance records, not project proofs.
- `KIP126/Mathlib/` is the optional Mathlib adapter layer.
  `KIP126/Checks/` is the regression and audit layer.

Challenge2 is defined in `KIP126/Interface/Challenge/Challenge2.lean`.
Its only fields are `literature` and `computation`. Literature has correlated
`bindings` and `results`; computation has `bindings` and `results` dependent
on that same literature delivery. Its presentation is a computation binding,
not a third root field. Def fixes the route, model and shared mathematical
background before either delivery. Main derives internal applications after
consuming the sole Challenge2 witness. Fixed-sphere applicability and
filtration separation are Def-owned theorems with explicit unfinished proofs;
downstream modules may reference their statements without adding them to
Challenge2. Reusable foundation language lives under `KIP126.Foundation`;
there is no Challenge1 stage or equality transport to a second implementation.
Do not create parallel witness definitions or proof transmission trees.

The current endpoint is standard `h_6^2` nonzero permanent survival. Geometry
(framed manifolds, Browder/Pontryagin--Thom comparison, and geometric Kervaire
existence/nonexistence) is outside the current scope and must not be restored
as Challenge2 fields or acceptance obligations without user approval. Preserve
the classical `theta_5`/`h_5^2` literature used by the selected proof route.

Intermediate spectra used only to certify computation conclusions, such as
`C2` and `Ceta`, belong to Interface's proof process. Do not add them to
Challenge2 or treat their absence as an interface-completeness failure.
Introduce their objects, data and comparisons only if the chosen proof needs
them; the existing model-bound computation conclusions must still be proved.

Do not create empty directories or placeholder modules merely to display the
architecture. Import a concrete module directly when a wrapper would only
re-export that one module and provide no required behavior. Multi-module
aggregators and required Lake library roots may remain.

## Proof-stage invariants

The sole Challenge/Solution theorem pair is
`Main/Challenge/h6_sq_permanent.lean` and
`Main/Solution/h6_sq_permanent.lean`, stating the standard final theorem.
The structure `Challenge2` itself specifies the Interface construction goal;
`Interface/Solution/Challenge2.lean` constructs a value of that type. Do not
add a duplicate placeholder theorem merely to restate this construction goal.

For each pair:

- The complete types must agree, including universes, variables, typeclass
  assumptions, explicit and implicit hypotheses, and conclusion.
- Update both sides in the same change whenever the statement changes.
- The Challenge declaration remains `theorem ... := by sorry`. Do not replace
  it with a proposition definition, fill its proof, or remove it because the
  Solution exists.
- The Solution proof must not invoke the Challenge placeholder, directly or
  indirectly. It must use shared definitions and genuine proof dependencies.

Internal stage obligations live only in the relevant Solution tree; do not
create intermediate Challenge mirrors or turn unfinished proof obligations into
new structure fields or axioms. Generic reusable mathematics remains in Def.

Each consumer uses one direct `Challenge2` witness and projects all
dependent data and compatibility facts from that same witness. Do not replace a
correlated package with independent axioms or make dependent fields choose
different base objects. Producer Solutions must not depend on the matching
consumer axiom.

## Trust boundary

The only project `axiom` is the temporary direct witness
`Main.Axiom.challenge2 : KIP126.Challenge2` in
`KIP126/Main/Axiom/Challenge2.lean`. It does not use `Nonempty` or a choice step.

Do not add project axioms under `Def/`, `Mathlib/`, `Checks/`, `LinProgram/`,
Challenge files, or Solution files. Do not convert an unfinished theorem into
an axiom to hide `sorryAx`.

External results must retain their hypotheses, scope, source locators, and
provenance. They remain explicit inputs bound to the same model through
`Challenge2.LiteratureResults` on its source bindings; do not replace them with untracked global
facts. Lean interfaces contain mathematical statements only. Source IDs,
locators, acquisition status and artifact hashes belong in the canonical
`docs/external-inputs.json` manifest, linked to Lean declarations and Blueprint
labels by external checks. Do not restore `ExternalResult`, `ExternalEvidence`,
or a parallel Lean source registry. Mathematical interpretation of computation
rows remains in Lean, independently of this metadata.

Generated records, successful hash checks, file moves, interface packaging, and
successful compilation are not proof-completion evidence. A declaration that
depends on `sorry`, a Challenge placeholder, or a project axiom must not be
presented as fully proved or marked complete in the Blueprint. Final acceptance
is governed by `PROJECT_BOUNDARY.md`.

## Lean source organization

Organize mathematical components under `KIP126/Def/` into `Data.lean`,
`Predicates.lean`, and `Proofs.lean` where those layers are useful:

- `Data.lean` owns mathematical objects, structures, operations, and
  constructions. It must not hide unfinished property proofs in data
  definitions.
- `Predicates.lean` owns definitions of mathematical conditions and relations.
- `Proofs.lean` owns lemmas and theorems about the data and predicates. It must
  not become the hidden home of new data or axioms.

Follow the dependency direction `Data -> Predicates -> Proofs`; later
components may import earlier proofs when constructing genuinely new data. Do
not introduce cyclic imports or turn provable properties into input hypotheses
to avoid this separation.

Preserve public declaration names during file organization unless the task
explicitly requires an API change. A compatibility adapter does not prove its
existence obligations, and generic Def modules must not import root Challenge
packages or consumer axioms merely to remove duplication.
