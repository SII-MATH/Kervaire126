# KIP126 proof work

Read `AGENTS.md` and `PROJECT_BOUNDARY.md` before mathematical work. They remain
the canonical architecture and trust rules. Do not change existing definitions,
interfaces or theorem statements to close a proof.

For automated batches use `.claude/workflows/kip126-batch.js` and the three
`kip126-*` skills. `Prover-all/README.md` documents the command-line tools.
The original checkout provides the pinned Lean environment and existing build
cache. Prepared runs bind its dirty and untracked non-ignored sources, but copy
only selected full Lean files into temporary workers, preserving module paths.
Workers have no Lake project or copied dependency cache. Provers edit only their
marked worker proof slots and the task worker support.json: the controller may
add existing acyclic lower-layer imports and closed private theorem helpers.
Original statements, definitions, imports and all other bytes stay frozen in
the worker; controlled support is materialized and checked separately. The original mathematical sources change only through an
explicit apply operation; prepare may update the original build cache.

The executable boundary is `scripts/kip126_proof_tools.py` plus the retained
`Prover-all/prover/` and `Prover-all/lean/Audit.lean`. Proof agents must not edit
these, run metadata, baseline audits, or project/toolchain configuration.
Skills describe procedures; they are not filesystem security boundaries.

Keep proof state separate from execution state: `verified`/`integrated` are
preview results against the unchanged baseline imports. `integrated` means a
staged patch, not a checked combined batch. Explicit apply writes the batch,
builds changed modules together and then audits their actual dependencies.
`local_only` and reduced direct sorry counts are not dependency closure.
Preserve the intentional `Main/Challenge` sorry and never use it in Solutions.

Reference design: https://github.com/qinz1yang/auto-formalizing-skills/tree/main/agents
We adopt scout/prover/refuter separation, evidence checks and failed-route notes.
We do not adopt signature restatements, unlimited retry budgets, mandatory large
agent waves, model pins, or assumptions about another runtime's tools.

Before long proof exploration, native Lean MCP must return the actual worker
goal and diagnostics; a server connection or stdio bridge alone is insufficient.
Small lemma searches stay with the Prover. Use narrow scratch handoffs only for
substantial research obstacles, and submit useful checked decompositions for
review without counting them as closed holes. Checkpoints are soft investigation
budgets, not undocumented runtime timeouts.

AGENTS.md delivery checks remain mandatory after accepted source changes. The
main session runs Blueprint synchronization/rendering and source/interface/stage
checks once after apply. Provers, Researchers and preview agents run only focused
Lean checks, not those delivery suites on every temporary draft.
