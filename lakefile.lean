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
Reuse the imported Milnor certificate kernel in place. These non-default
libraries expose only the certificate kernels used by the local algebra checks;
the imported research project and its generated batches are not build targets.
-/
lean_lib MilnorCertificates where
  srcDir := "Lin-program/program"
  roots := #[`MilnorCertificates.StableProduct]
  globs := #[.one `MilnorCertificates.Basic, .one `MilnorCertificates.Grading,
    .one `MilnorCertificates.WindowSoundness, .one `MilnorCertificates.RankStability,
    .one `MilnorCertificates.Import, .one `MilnorCertificates.GeneralTactic,
    .one `MilnorCertificates.StableProduct,
    .one `MilnorCertificates.Frobenius, .one `MilnorCertificates.GeneratorEvaluation,
    .one `MilnorCertificates.FoldEvaluation, .one `MilnorCertificates.Coassociativity,
    .one `MilnorCertificates.TriangleReindex, .one `MilnorCertificates.IteratedEvaluation,
    .one `MilnorCertificates.ExponentEncoding, .one `MilnorCertificates.PolynomialExtraction]

lean_lib LinProgramCertificates where
  srcDir := "Lin-program/program"
  roots := #[`LinProgramCertificates.Tactic]
  globs := #[.one `LinProgramCertificates.Verifier, .one `LinProgramCertificates.Tactic]

lean_lib NamedElementCertificates where
  srcDir := "Lin-program/program"
  roots := #[`NamedElementCertificates.ModuleEvaluation]
  globs := #[.one `NamedElementCertificates.Basic,
    .one `NamedElementCertificates.Evaluation, .one `NamedElementCertificates.ModuleEvaluation]

/-!
Optional compiled-environment audit for final proof acceptance.
Development CI checks compilation without treating unfinished proofs as complete.
-/
lean_exe axioms where
  root := `scripts.Axioms
