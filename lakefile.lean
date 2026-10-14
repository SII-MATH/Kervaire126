import Lake
open Lake DSL

package KIP126 where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

/-!
`leanblueprint checkdecls` shells out to this executable.  Pin the dependency
instead of following its default branch so declaration checking is reproducible.
-/
require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git" @
    "3d425859e73fcfbef85b9638c2a91708ef4a22d4"

@[default_target]
lean_lib KIP126 where
  globs := #[.andSubmodules `KIP126]

/-! Optional independent historical library, restored from backup by user request.
It is outside the KIP126 import graph and is not a default or CI target. -/
lean_lib KIPBase where
  -- checkdecls imports every library root. Keep this optional library out of
  -- the KIP126 declaration-checking environment; explicit globs still build it.
  roots := #[]
  -- A nested standalone workspace may contain KIPBase/.lake. Recursive globs
  -- at KIPBase itself would compile those ignored dependency sources as local
  -- modules. Cover every owned source area explicitly, without deleting caches.
  -- scripts.test_kipbase_build_layout guards source coverage as the tree grows.
  globs := #[
    .one `KIPBase,
    .one `KIPBase.Basic,
    .one `KIPBase.Check,
    .one `KIPBase.CheckBasic,
    .one `KIPBase.E2page,
    .one `KIPBase.E2pageCompute,
    .one `KIPBase.E2pageData,
    .one `KIPBase.E2pageExamples,
    .one `KIPBase.E2pageTactic,
    .one `KIPBase.E2pageTacticExamples,
    .one `KIPBase.Mathlib,
    .one `KIPBase.ModelRealizationChecks,
    .one `KIPBase.Standalone,
    .one `KIPBase.chanllege,
    .submodules `KIPBase.Compatibility,
    .submodules `KIPBase.Section7,
    .submodules `KIPBase.Section8,
    .submodules `KIPBase.SpectralSequence,
    .submodules `KIPBase.StableHomotopy,
    .submodules `KIPBase.Synthetic,
    .submodules `KIPBase.multiplicativeSS]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`backward.defeqAttrib.useBackward, true⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩]

/-!
Optional compiled-environment audit for final proof acceptance.
Development CI checks compilation without treating unfinished proofs as complete.
-/
lean_exe axioms where
  root := `scripts.Axioms
