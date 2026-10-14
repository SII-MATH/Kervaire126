# Kervaire126 agent guidance

## Start here

- The Blueprint is the mathematical plan, not evidence that a proof is complete.
- Blueprint nodes describe mathematical objects, statements, and proof
  dependencies.
- A mechanical cleanup must not silently change a public declaration, a
  stage-boundary statement, source provenance, proof status, or mathematical
  strength.

## Check and restore GitHub Release caches after pulling updates

Every time you pull remote repository updates, also check this repository's
GitHub Releases for a project build cache matching the updated checkout.
After a successful `git pull` (or fetch followed by merge/rebase), perform this
check as part of the same update task, even if no compilation is requested.
If a compatible cache is available and is not already verified locally,
download, verify, and restore it using the steps below. Reuse an already
verified compatible local cache without downloading it again.
Run the following from the repository root after updating the checkout:

```bash
gh release list --repo SII-MATH/Kervaire126 --limit 100 \
  --json tagName,isDraft \
  --jq '.[] | select(.isDraft == false and (.tagName | startswith("build-cache-"))) | .tagName'
```

The initial Linux x86_64 cache is
[`build-cache-d8eb0ee60769-linux-x64`](https://github.com/SII-MATH/Kervaire126/releases/tag/build-cache-d8eb0ee60769-linux-x64),
built from commit `d8eb0ee60769457c5d6e6a155fd8c029f4eb53e9` with
`leanprover/lean4:v4.32.2`. Before downloading large parts, inspect its `metadata.json` (use
`gh release download <tag> --repo SII-MATH/Kervaire126 --pattern metadata.json
--dir <temporary-directory>`). For that cache, download and verify using:

```bash
(
  set -euo pipefail
  cache_dir=$(mktemp -d)
  gh release download build-cache-d8eb0ee60769-linux-x64 \
    --repo SII-MATH/Kervaire126 --dir "$cache_dir"
  (cd "$cache_dir" && sha256sum --check SHA256SUMS)
  cat "$cache_dir"/project-build.tar.gz.part-* > "$cache_dir/project-build.tar.gz"
  printf 'Verified parts; inspect metadata and restore from: %s\n' "$cache_dir"
)
```

- Select a cache for the checked-out source, not merely the newest release.
  Inspect `metadata.json`: match repository, OS/architecture, Lean toolchain and
  `lake-manifest.json` hashes. Compare its `input_fingerprint` with
  `python3 scripts/ci_build_artifact.py fingerprint` and verify the joined
  archive's SHA-256 against `archive_sha256` before unpacking.
- An `AGENTS.md`-only change changes the full-tree fingerprint but does not change
  Lean build inputs. Confirm that exception with
  `git diff --exit-code <source_commit> -- . ':(exclude)AGENTS.md'`.
  Other source changes mean the archive is only an incremental baseline;
  Lake must rebuild affected modules. Never claim an exact cache match then.
- Restore only when no build is writing `.lake/build/`. Use the existing
  `unpack_tar` helper in `scripts/ci_build_artifact.py` to extract into a temporary
  staging directory; it checks paths and entry types. Preserve any existing
  local build directory as a backup before installing the staged `.lake/build/`.
  Do not discard newer local compilation progress to install an older cache.
  The script's `restore` CLI handles CI artifacts, not Release downloads.
- This release contains only project `.lake/build/` products. Obtain pinned
  dependencies and their Mathlib cache separately as described in `docs/CI.md`.
  When a build is subsequently requested, still run the normal build command
  (normally `lake build KIP126 checkdecls`); a downloaded cache is not a successful
  build or evidence that the mathematical proofs are complete.
- If no compatible release exists or GitHub is unavailable, report that briefly
  and finish the source update using the available local caches. Do not block
  the update on an optional cache download. Plain `git pull` does not download
  Release assets; perform the cache check and restoration explicitly as part
  of each pull/update task.

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
By explicit user decision, `KIPBase/` and `KIPBase.lean` are restored as an
independent optional library. Do not import KIPBase into KIP126, add it to the
default build or CI, or treat its historical assumptions as KIP126 proofs.
Do not restore historical `backups/`, `docs/archive/`,
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
- Optional Mathlib spectral-sequence adapters are maintained in the legacy
  `SII-MATH/KIP126` repository. Do not restore `KIP126/Mathlib/` or its adapter
  exports here. Upstream Mathlib remains a dependency of the mathematical core.
- `KIP126/Checks/` is the regression and audit layer.

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

Within the KIP126 proof and acceptance boundary, the only project `axiom` is the temporary direct witness
`Main.Axiom.challenge2 : KIP126.Challenge2` in
`KIP126/Main/Axiom/Challenge2.lean`. It does not use `Nonempty` or a choice step.
Restored KIPBase retains its historical axioms in its independent namespace;
they must not enter the KIP126 dependency graph or acceptance evidence.

Do not add project axioms under `Def/`, `Checks/`, `LinProgram/`,
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
