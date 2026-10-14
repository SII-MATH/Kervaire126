# Complete native module-map replay

This package reconstructs finite ideal-combination witnesses from the pinned
v126.3.cw49 entities and prepares Lean certificates for the complete native
module maps. Preparation and Python witness checks do not certify a quotient
map. A complete result requires the whole Lean relation theorem, the quotient
map, and the final import/axiom audit to pass in the recorded fixed snapshot.
The actual spectrum-map comparison remains uncertified in every mode.

## Requirements and outputs

Use a KIP126 checkout containing its pinned source entities, `unrar`, Python
3.10 or later, and the repository's Lean/Lake toolchain on `PATH`. The runner
checks the external mathematical imports with one serial Lake build before
starting the isolated direct-Lean workers. Coordinate that freshness build with
other Lake builds in the same checkout. Use two workers for the production
replays described here.

Run the commands below from this package directory, replacing the absolute
checkout and output paths with local paths. An installed package can infer its
repository root; an independent copy needs `--root`. Keep generated output in
a separate directory. Preparation and replay take the same exclusive output
lock, so a live replay rejects regeneration of its inputs.

The generated manifest records the complete source coverage, original source
and graph identities, witness bytes, generation inputs, generated source hashes,
and dependency graph. A moved checkout or tool package must regenerate its
manifest; paths are part of the replay identity. Old receipts are reusable only
when their complete input keys and output hashes still match.

## Ceta to sphere

```sh
python replay-ceta.py --root /absolute/path/to/KIP126 --output-dir /absolute/path/to/ceta-replay --prepare-only
python replay-ceta.py --root /absolute/path/to/KIP126 --output-dir /absolute/path/to/ceta-replay --check
python replay-ceta.py --root /absolute/path/to/KIP126 --output-dir /absolute/path/to/ceta-replay --jobs 2
```

The first command rebuilds the untrusted witness from the pinned original
entities and generates every source module. The second independently rebuilds
the witness and compares all expected output bytes without compiling. The
third prepares the same data and runs the full Lean target. Repeating it resumes
only validated receipts. `--target` selects a generated module and all its
dependencies; a proper subset never certifies the complete map.

Ceta coverage is all 887 official generator images and all 76,569 original
source relations, split into 150 source blocks. The reconstructed witness has
75,347 nonzero-image rows, 1,222 formally zero-image rows, and 167,453 recorded
ring-relation multiplication steps. These are independently reconstructed
algebraic combinations, not a C++ execution trace. Its 17,417,952 bytes have
SHA-256 `a89a0ae1fe00ed8f255f05a3f829874028039df22febc407f09327909d65ddd1`.

The portable plan contains **266 generated Lean modules**. The original
temporary production plan contained 267 because it also generated
`ModuleMaps.Support`. This package imports that same support module from the
repository. All other 266 generated Lean source files have identical bytes;
the relation coverage and final theorem are unchanged.

The final theorem `KIP126.LinModule.CetaToSphere.all_relations_zero` quantifies
over the whole original Ceta relation list. It constructs `nativeMap` out of
the complete quotient, together with the laws for every original generator and
native monomial, and uniqueness. The official graph directly determines every
generator image. A recorded empty image is zero; a missing image is never
defaulted to zero.

## CW to Ceta

```sh
python replay-cw.py --root /absolute/path/to/KIP126 --output-dir /absolute/path/to/cw-replay --prepare-only
python replay-cw.py --root /absolute/path/to/KIP126 --output-dir /absolute/path/to/cw-replay --check
python replay-cw.py --root /absolute/path/to/KIP126 --output-dir /absolute/path/to/cw-replay --jobs 2
```

These commands prepare the shared Ceta source package inside
`cw-replay/shared-ceta`, so no earlier temporary audit file or generated package
is required. Alternatively, pass `--shared-ceta /absolute/path/to/ceta-replay`
to read an existing generated Ceta package without regenerating it. The CW
generator authenticates every reused source and reconstructs any additional
sphere-relation bridge needed by its own full witness.

CW coverage is all 844 official images in the original 887-generator Ceta
target and all 69,263 original source relations. Its independently rebuilt
witness has 67,929 nonzero-image rows, 1,334 formally zero-image rows, and
238,883 relation multiplication steps. Its 22,137,931 bytes have SHA-256
`48dea38ed810cb3458ba6c7862d594f421e1bf38e8bb813862e654ed125967e6`.
The portable plan has **434 generated Lean modules**, compared with the
original temporary plan's 437. All 434 are byte-identical to their original
counterparts; `Support`, `ModuleSupport`, and `ModuleTerms` are now imported
from the repository. It retains the original coefficient algebra and every
original source and target relation; support compression never substitutes a
smaller quotient for the full target.

The CW preparation manifest keeps `quotient_map_certified` false. As for Ceta,
only the runner's complete final Lean/audit result can set the separate
`complete_native_quotient_map_certified` status flag to true.

## Fixed replay and receipts

The common runner serves both maps. Before freshness and again before marking
a run complete, it invokes the trusted generator in this package to reconstruct
and compare the entire expected manifest and every generated source. It also
requires the fixed final theorem, final audit, every original relation block,
and their full dependency closure. An empty, truncated, or relabeled job list
cannot become a complete-map certificate merely because all its listed jobs
finished.

The runner hashes the compiler/runtime, transitive external artifact families,
generated sources, fixed input files, and generated dependencies. It copies
external artifacts and generated sources to byte-verified, read-only,
content-addressed directories. Lean imports only that frozen library and the
isolated generated output directory. Namespace resolution and every used
artifact are checked before and after each job. Only a successful direct Lean
invocation with successful postflight checks receives a reusable receipt.

`status.json` records the current phase, module counts, runner PID, and the two
distinct certification flags. `running/` records Lean process details;
`progress.jsonl`, `logs/`, and `receipts/` retain compilation evidence. A stopped
process can leave a historical running status: verify the process is still
alive before reporting that a replay is active.

```sh
python runner.py --output-dir /absolute/path/to/ceta-replay --status
```

This command reports historical status and whether its manifest still matches;
it does not rerun Lean. `complete_native_quotient_map_certified` becomes true
only after every planned module and final audit pass. Module counts include
support and sphere-relation bridges and must not be reported as counts of
certified source relations. `actual_spectrum_map_comparison_certified` always
remains false.

The final audit rejects imports from actual-model/delivery layers and permits
only `propext`, `Classical.choice`, and `Quot.sound` among axioms. Successful
preparation, source equality, or partial blocks do not replace this audit.

## Regressions

```sh
python test_runner.py
python test_replay.py
python test_complete_plan.py
python test_cw.py
```

These tests check receipt invalidation, namespace and artifact shadowing,
frozen/transitive dependency changes, missing or failed compiler outputs, stale
completion status, generation-input drift, and entry-point lock exclusion.
Complete-plan regressions cover empty and precheck-only plans, missing final or
audit modules, omitted original relation blocks, altered kinds and dependency
edges, failed independent reconstruction, and proper subset targets.
Their mocked output is confined to temporary fixtures and never counts as
mathematical proof or a production receipt.
