module

public import KIP126.Interface.Solution.LinProgram.AdamsOneLine.H4
public import Lean.Elab.Command

@[expose] public section


/-! A nonzero actual-sphere producer slice, independent of the consumer
witness and of total table certification. The fixed Def implementation still
has its admitted foundational dependencies; they are reported explicitly. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod ||
        mod == `KIP126.Interface.Solution.Challenge2 ||
        mod == `KIP126.Interface.Solution.LinProgram.Basis.Certification ||
        mod == `KIP126.Interface.Solution.LinProgram.Multiplication ||
        mod == `KIP126.Interface.Solution.AdamsOneLine then
      throwError "one-line producer imported a consumer or admitted result: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Core.Algebra.eq_zero_or_of_span_singleton,
      ``KIP126.Core.Algebra.LinearEquiv.zero_or_of_exhaustion,
      ``KIP126.Core.Algebra.LinearEquiv.image_eq_of_exhaustion,
      ``KIP126.LinE2.E2At_eq_zero_or_of_span,
      ``KIP126.Classical.Adams.MilnorCohomology.hiCochain_ne_zero,
      ``KIP126.Classical.Adams.MilnorCohomology.hi_ne_zero,
      ``KIP126.Classical.Adams.MilnorCohomology.internal_hi_ne_zero,
      ``KIP126.LinE2.OneLine.E2At_h4_eq_zero_or,
      ``KIP126.LinE2.OneLine.E2At_h0h3Sq_eq_zero_or,
      ``KIP126.LinE2.OneLine.h4Row_mem,
      ``KIP126.LinE2.OneLine.targetRow_mem,
      ``KIP126.LinE2.OneLine.h4_value,
      ``KIP126.LinE2.OneLine.target_value] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in independent one-line certificate {decl}: {ax}"
  let modelAxioms ← collectAxioms ``KIP126.Classical.Adams.sphereAdamsModel
  for decl in [``KIP126.Interface.Solution.LinProgram.sphereH4_standard_class,
      ``KIP126.Interface.Solution.LinProgram.sphereH0H3Sq_standard_class,
      ``KIP126.Interface.Solution.LinProgram.row5434_hasNonzeroDifferential,
      ``KIP126.Interface.Solution.LinProgram.row5434_rejects_zero,
      ``KIP126.Interface.Solution.LinProgram.row5434] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax || modelAxioms.contains ax do
        throwError "producer adds an axiom beyond the fixed Def model: {decl}: {ax}"

set_option maxRecDepth 2048 in
example : KIP126.Computation.LinProofs.RawData.lookup 0 1 =
    some ⟨5434, "d2", 1, 16, 2, [0], [0]⟩ := rfl

/-- A nonzero actual target cannot be substituted by zero. -/
example (literature : KIP126.Challenge2.LiteratureInterface)
    (P : KIP126.Classical.Adams.LinE2Presentation) :
    P.comparison 3 17 (by decide) KIP126.LinE2.OneLine.dataH0H3Sq ≠ 0 := by
  rw [KIP126.Interface.Solution.LinProgram.sphereH0H3Sq_standard_class literature]
  exact KIP126.Interface.Solution.LinProgram.sphereH0H3Sq_ne_zero literature

#print axioms KIP126.LinE2.OneLine.E2At_h0h3Sq_eq_zero_or
#print axioms KIP126.Interface.Solution.LinProgram.row5434_hasNonzeroDifferential
#print axioms KIP126.Interface.Solution.LinProgram.row5434
