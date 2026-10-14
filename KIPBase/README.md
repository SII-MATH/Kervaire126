# KIPBase

`KIPBase` is an independent Lean/Lake project embedded in the Kervaire126 checkout.
It uses Lean 4.32.2 and Mathlib 4.32.2, matching the parent project.

The source was restored from `codex/local-backup-20261013` (`4977ff53b`)
by user request. From the repository root, `lake build KIPBase` explicitly
builds this optional library. It is not a default or CI target; its historical
axioms and unfinished comparisons are outside KIP126's proof acceptance.
KIP126 does not import this library. No historical backup archives or
KIPBase-specific CI tools were restored.

From this directory, initialize dependencies and build with:

```sh
lake exe cache get
lake build
```

The default target imports the core, synthetic, stable-homotopy, and
multiplicative spectral-sequence developments through `KIPBase.Standalone`.
`KIPBase.Compatibility.FilteredComplex` is excluded from that target:
it imports KIP126's representative layer and is built by the parent project.

## Reuse in KIP126

The active component provides general spectral-sequence and filtered-complex
constructions, stable-homotopy and synthetic interfaces, and multiplicative
spectral-sequence tools. Concrete Adams and synthetic inputs still include
explicit assumptions. A reusable proof must be checked against its actual
parameters, model, grading, page convention and dependency assumptions.
Compilation or an absence of local placeholders does not establish that it
proves the corresponding KIP126 paper statement.

KIP126's fixed internal sphere sequence is constructed in
[TowerSSData/Sequence/Data.lean](../KIP126/Def/ClassicalAdams/TowerSSData/Sequence/Data.lean)
and specialized on its own Def background. Its route objects are correlated by
[Route.Model](../KIP126/Def/Kervaire/Route/Model/Coherent/Data.lean).
The compatibility module does not assert a global equivalence of all pages
and abutments of the two libraries.

The KIP126 scope and acceptance boundary is documented in
[PROJECT_BOUNDARY.md](../PROJECT_BOUNDARY.md); the restored-library boundary
and current module responsibilities are in [AGENTS.md](../AGENTS.md) and
[REPOSITORY.md](../docs/REPOSITORY.md). Source comments retain the original
provenance; historical migration reports are not part of this source tree.
