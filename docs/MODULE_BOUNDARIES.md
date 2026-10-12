# Public module boundaries and mathematical handoffs

The repository uses one `lean_lib KIP126`; individual Lean source files remain
the compilation units. The seven maintenance owners and twenty milestones are
responsibility assignments. They do not create compiler boundaries by themselves.
This registry connects selected mathematical handoffs to real public declarations,
their importing consumers, and the implementation access that remains intentional.

The implementation baseline is
[`develop@cea451f2`](https://github.com/SII-MATH/Kervaire126/tree/cea451f2c4b29a966bffa43bce3ca9438f8e5565).
The design references come from the
[milestone website](https://kip126-milestones.surenny233.chatgpt.site/) and its
[published data](https://kip126-milestones.surenny233.chatgpt.site/review-data.json),
which still describe `85d7138`. The data's SHA-256 and source commit are retained
in [module-boundaries.json](module-boundaries.json). The mapping contains all
90 contract groups, all 480 candidate NL–FL IDs, and M01–M20. It does not assert
that the old website's source paths or proposed signatures are current code.

## Three independent states

Each registered delivery records three separate states:

| State | What it establishes | What it does not establish |
| --- | --- | --- |
| `mathematical_review` | Whether an expert has accepted this particular NL–FL contract | A source extraction or a compilation is not expert approval |
| `public_boundary` | Which public name and file currently provide the handoff | A public theorem may retain unfinished upstream obligations |
| `build_isolation` | Recorded evidence from an actual incremental-build experiment | Import statistics do not measure time saved or files reused |

Mathematical reviews remain pending. Build isolation remains unmeasured unless
the registry cites a completed experiment. The implementation status describes the
source change and distinguishes it from unimplemented parts of the website
proposal. A supporting implementation formula is explicitly marked as such; it is
not presented as the identical statement of a broader NL–FL entry.

This file does not replace `docs/external-inputs.json`, introduce a second source
registry, or reproduce the scheduling and approval workflow in the pending
[milestone PR #3](https://github.com/SII-MATH/Kervaire126/pull/3).

## Seven maintenance owners

The contract mapping, rather than a namespace's spelling, determines mathematical
ownership. Existing namespaces remain compatible. For example, the implementation
of `KIP126.Main.Solution.Tools.shifted_finite_source_exists` is in `Def`.

| Owner | Contracts and milestones | Source responsibilities |
| --- | --- | --- |
| `steenrod` | M01.steenrod, M01.cobar | Steenrod and the reusable algebra supporting it |
| `spectral` | M03.page_api, representatives, ambiguity | Generic spectral-sequence and filtered-complex language |
| `adams` | Remaining M01, M02, and the actual-Adams/extension portions of M03 | Fixed classical and synthetic systems, stable-homotopy foundations, comparisons, actual E₂ and representatives |
| `literature` | M04 | Correlated literature bindings and the 48 source-result fields |
| `computation` | M05, M06, M08 | Pinned Lin data and certificates, fixed interpretation, and consumer-facing computation facts |
| `rules` | M03.shifted_finite_source; generic portions of M07; M09–M11 | Reusable extension rules, representation arguments, and source-to-model transport |
| `main` | M07.nu_source/application; M12–M20 | Paper-specific reasoning, the same weak representative, divisibility, rigidity, and the standard endpoint |

The JSON records all ninety assignments individually, including milestones split
between owners. Its longest-path ownership rules provide administrative defaults
for the global import report. These defaults do not mean every declaration in a
mixed legacy file belongs to the same mathematical contract. `Checks` and the
library's aggregate root are audit/build infrastructure, not an eighth owner.
The established Def / Interface / LinProgram / Main architecture remains checked
by `test_stage_boundary_layout.py`.

## Implemented public handoffs

| Handoff | Public declaration and provider | Consumer and retained mathematical contract |
| --- | --- | --- |
| M08, `I-8b5db474016d` | `Section7.h5_square_times_entire_770_zero` in `Main/Solution/Route/Section7/ThetaMassey.lean` | `ThetaToda` uses the public statement. The result quantifies over **every** element of E₂(7,70) and gives zero in E₂(9,134). |
| M16, `I-81ecf4ddd9fa` | `Section7.weak_y_exists` in `Main/Solution/Route/Section7/WeakY.lean` | `NuTarget` receives **one** y in π(125,132)Q₉ together with its Y detection and λ²(h₀·y) ≠ 0. |
| M03, `I-04d3f44f5b4b` | `Main.Solution.Tools.shifted_finite_source_exists` in `Def/Kervaire/Route/Tools/PageExtensionStretching/Proofs.lean` | `GeneralizedMahowald/Proofs` uses the public statement with the original `SyntheticInputs` premise. |
| May source adaptation | `StableHomotopy.connectingHomomorphism_eq_desuspend` in `Def/StableHomotopy/Context/Connecting/Desuspension/Proofs.lean` | `Interface/Solution/Literature/Route/May` uses the existing formula and preserves the signed boundary. This supports M04.may; it is not a new version of that source field. |
| Existing filtered-differential example | `FilteredComplex.pageDifferential` in `FilteredDifferential/Data.lean`, and representative formulas in `FilteredDifferential/Proofs.lean` | The definition retains `@[no_expose]`. Component proofs open it internally; spectral-sequence construction uses public formulas and successor/square-zero laws. |

The first three rows link to proposed website entries while preserving the
current mathematical statements. There are explicit limits to that correspondence:

- **M08:** the existing generic `Inputs D L G` theorem and its namespace remain.
  The proposed fixed `Challenge2` / `ActualE2At` / `actualE2Product` signature and
  relocation of the computation proof have not been claimed as completed. The
  entire-grid result must never be replaced by `h5Sq_B_zero`: B has degree (8,70),
  with product in (10,134), and is a different statement.
- **M16:** the new theorem uses the existing sole fixed `Challenge2` witness.
  Its detection and nonzero product are in the same existential quantifier. The
  website's explicit arbitrary `input : Challenge2` signature needs corresponding
  parameterization of its upstream public results and remains separate work.
- **M03:** making the existing statement public removes Mahowald's private import.
  It does not claim the proposed reduction from `SyntheticInputs` to only
  `DifferentialRigidity` and `FiniteQuotientPageVanishing`.

M18 keeps its original `TargetNuDivisible` conclusion on the untruncated sphere:
t in π(125,139)S and a in π(122,132)S, with (λν)·a = λ⁴t. Its own P/Q lifting
implementation may remain private to M18. It must not reconstruct the weak y
from M16's private helpers. The final Challenge/Solution pair, the fixed standard
model, the correlated literature/computation package, and the two root
`Challenge2` fields are unchanged.

## Public environment and allowed unfolding

`Common.lean` publicly supplies the fixed StageInput and Section7 predicates.
Additional proof dependencies live in `ProofSupport.lean`, which is imported
ordinarily by the relevant implementation files. Private helper files similarly
keep their own proof imports ordinary. `Section7.lean` may explicitly aggregate
public mathematical results; it does not need to reexport the helper files.

The public-environment reduction does not detach the paper from its actual
standard foundation. StageInput still has a substantial public dependency
closure. Counts of removed direct imports must not be reported as if they were
the number of foundational files isolated from downstream compilation.

Each delivery's `public_environment` lists the objects, typeclasses, predicates,
and shared choices required by its statement. `unfolding_policy` distinguishes:

- A public theorem whose proof body is hidden by `module`.
- A public definition explicitly marked `@[no_expose]`, whose clients use proved
  operation formulas.
- Existing exposed definitions and abbreviations whose definitional equality
  still forms part of their public use. These are not hidden wholesale.

The `@[expose] public section` syntax does not by itself expose every theorem
proof. Conversely, `noncomputable def` does not by itself hide a definition.
The filtered differential demonstrates the intended operation/formula boundary.
One public statement and its proof can remain in the same file. Changes to other
public declarations in that file still share the same compilation unit.

## Enforced source checks

Run:

```sh
python3 scripts/module_boundaries.py --check
python3 -m unittest scripts.test_module_boundaries
```

The standard `scripts/check.sh` includes both. A full machine-readable import
inventory, including the modes on each edge and actual direct importers of
registered providers, can be written with:

```sh
python3 scripts/module_boundaries.py --report metrics/module-boundaries.json
```

The scanner preserves ordinary, `public`, `meta`, and `all` distinctions. It
reads the token sequence rather than assuming one command per line: modifiers
can cross newlines and nested block comments. Lean 4.32 permits one module name
per import command. Strings and `«quoted module identifiers»` are handled
lexically; redundant quoting cannot hide a project import. The report is a
source graph, not an elaborated constant dependency graph.

Every project `import all` has an exact consumer/provider registration and a
reason. An unregistered edge fails, including a new edge between maintenance
owners. There are no wildcard exceptions. Registrations distinguish:

- `component_internal`: the producer reads its own construction to prove the
  public handoff, such as the filtered differential or M16's joint witness.
- `existing_debt`: a named baseline access still awaiting an adequate public
  formula; retaining it is not an assertion of complete isolation.
- `audit`: a Checks-only inspection of proof details.

Registered consumers may not `import all` or `open private` their provider.
They may not reach a designated private implementation through public reexports
or a direct helper import. The producer's ordinary proof imports are allowed:
reading a public theorem is precisely the intended boundary.

Production files may not reach `KIP126.Checks` or `KIP126.Checks.*`, including through intermediary
modules. The existing `KIP126.lean` aggregate root can include checks for the
full-library build; a production module importing that root is still rejected
if it inherits a path to Checks. Retired private-edge registrations are reported
for removal. Regression tests exercise attempted reintroduction of private
access, public bridge leakage, hidden-definition exposure, and audit backdoors.

## Compilation evidence and further work

`KIP126/Checks/ModuleBoundaries/PublicHandoffs.lean` is the Lean-level place to
check complete public types by ordinary imports. A passing compilation verifies
that those signatures can be consumed. It does not prove the absence of
`sorryAx`, validate NL–FL alignment, or measure incremental build reuse.

The six warm-build experiments are implemented in
[`scripts/benchmark_module_boundaries.py`](../scripts/benchmark_module_boundaries.py).
Run them from the repository root after a successful project build:

```sh
lake build KIP126 checkdecls
python3 scripts/benchmark_module_boundaries.py \
  --output metrics/module-boundary-benchmark
```

For each of M08 (`ThetaMassey` → `ThetaToda`) and M16 (`WeakY` → `NuTarget`),
the script makes three temporary changes: a public theorem's proof, an internal
helper's proof, and a public theorem's statement. Each experiment keeps the
consumer source unchanged and restores both source files and the project build
artifacts to the same warm baseline afterward. The report records Lean
expression hashes, artifact hashes and timestamps, Lake build/replay actions,
elapsed time, and exact patches. These measurements distinguish public
interface reuse from legitimate invalidation after a statement changes.

CI runs these experiments and uploads their report and logs as the
`module-boundary-benchmark` artifact. The experiments are implemented, but their
compilation results remain pending CI; the registry's `build_isolation` status
therefore remains `not_measured` until evidence from that run is recorded.
Failed or unavailable experiments must stay explicit. Historical cold-build
and cache-hit times are not evidence from this experiment.

Unimplemented proposal work is also listed in the JSON. In particular, standard
E₂ unfolding policies, arbitrary-input parameterization, M03's narrower premise,
and remaining private accesses require focused follow-up. This change establishes
real public handoffs and an enforceable import policy while retaining the
repository's current mathematical obligations and proof status.
