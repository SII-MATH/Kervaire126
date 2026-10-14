# Complete seed 5487 native composition replay

This package generates and replays the entire fixed 96-row dependency closure at
its original Milnor rank eight. When the full replay succeeds, its final theorem is
`KIP126.Computation.Secondary.Seed5487.Full.allNativeRows_composition_certified`:
for every native row it proves the original `compose` statements for `d ∘ d`,
`d ∘ f` and `f ∘ d`, with every target generator and rank-eight monomial retained.
The separate auxiliary parity theorem compares the extracted finite witnesses.
It does not establish the independent secondary associator formula, resolution
exactness/minimality, or a comparison with the actual sphere Adams differential.

The two fixed SQLite snapshots live in
`KIP126/LinProgram/Raw/Secondary/Seed5487/`. They are the previously audited output
of the unmodified published program, not separately published databases. Their
exact bytes, source archive, original rebuild record and selected Lean input are
linked in `docs/external-inputs.json`. Fresh program runs may have different
SQLite timestamp bytes; these commands replay the fixed snapshots.

Run from a checkout with the pinned Lean/mathlib toolchain, the source archive and
both database payloads available (Git LFS pointers alone are rejected):

```sh
secondary_root=$(git rev-parse --show-toplevel)
secondary_package="$secondary_root/KIP126/LinProgram/Translate/secondary-seed5487-certificates"
secondary_raw="$secondary_root/KIP126/LinProgram/Raw/Secondary/Seed5487"
secondary_run=$(mktemp -d /tmp/lin-secondary-5487.XXXXXX)
python3 -B "$secondary_root/KIP126/LinProgram/Translate/extract-secondary-witness.py" \
  --resolution "$secondary_raw/S0_Adams_res.db" \
  --secondary "$secondary_raw/S0_Adams_d2.db" \
  --output "$secondary_run/witness.json"
python3 -B "$secondary_package/generate.py" --root "$secondary_root" \
  --witness "$secondary_run/witness.json" --output-dir "$secondary_run" \
  --resolution-db "$secondary_raw/S0_Adams_res.db" \
  --secondary-db "$secondary_raw/S0_Adams_d2.db"
python3 -B "$secondary_package/replay.py" --output-dir "$secondary_run" --jobs 2
python3 -B "$secondary_package/replay.py" --output-dir "$secondary_run" --status
```

The fixed plan contains 328 modules: 39 complete degree tables, 271 blocks covering
all 15,839 ordered products, all 288 row compositions in 12 blocks, their support,
and the final theorem and axiom audit. Shared tables and balanced product lookup
change evaluation cost only. Every product certificate concludes the original
`MilnorCertificates.IsMilnorProductAll`. Each composition checks its entire
original path list; unavailable images or products cause failure. The two absent
base lifts, IDs 0 and 524288, are explicit empty base definitions, not defaults
for other missing records.

`replay.py` reuses the byte-pinned module-map runner's dependency freezing,
exclusive execution lock, Lean invocations and validated success receipts. It
requires independent full source regeneration before execution and completion.
A partial `--target` run cannot certify the complete plan. Successful completion
includes `Full.CompositionChecks`, which checks all row IDs and the transitive
axioms of the full theorems against the standard three logical axioms.

`status.json` sets `full_native_96_composition_certified` only after all jobs,
including the final theorem and audit, actually succeed. Both
`secondary_associator_certified` and `actual_d2_certified` remain false.
`--status` reports a historical fixed-snapshot result and does not rerun Lean.
Generation and the following source checks alone do not certify any theorem:

```sh
python3 -B "$secondary_package/generate.py" --root "$secondary_root" \
  --witness "$secondary_run/witness.json" --output-dir "$secondary_run" \
  --resolution-db "$secondary_raw/S0_Adams_res.db" \
  --secondary-db "$secondary_raw/S0_Adams_d2.db" --check
python3 -B -m unittest discover -s "$secondary_package" -p 'test_*.py'
```

The generator regressions independently re-extract the witness from the fixed
repository snapshots. Runner control-flow regressions use a synthetic complete
plan and mocked compilation; those tests are not Lean certificates.
