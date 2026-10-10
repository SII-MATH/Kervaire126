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

/-!
Optional compiled-environment audit for final proof acceptance.
Development CI checks compilation without treating unfinished proofs as complete.
-/
lean_exe axioms where
  root := `scripts.Axioms
