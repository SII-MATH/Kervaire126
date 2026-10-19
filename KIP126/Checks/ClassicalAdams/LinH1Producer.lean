module

public import KIP126.Interface.Solution.LinProgram.Hopf.H1Comparison
public import Lean.Elab.Command

@[expose] public section


/-! Audit the actual h₁ coordinate bridge. Generic cobar nonvanishing and
fixed-data exhaustion admit no nonlogical axioms; the fixed-model application
is limited to the existing model's admitted construction dependencies. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod ||
        mod == `KIP126.Interface.Solution.Challenge2 ||
        mod == `KIP126.Interface.Solution.LinProgram.Basis.Certification then
      throwError "h1 producer imported a consumer or admitted certificate: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinE2.E2At_h1_eq_zero_or,
      ``KIP126.Classical.Adams.MilnorCohomology.hi_ne_zero,
      ``KIP126.Classical.Adams.MilnorCohomology.internal_hi_ne_zero] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in independent h1 theorem {decl}: {ax}"
  let modelAxioms ← collectAxioms ``KIP126.Classical.Adams.sphereAdamsModel
  for decl in [``KIP126.Interface.Solution.sphereH1_exhaustive,
      ``KIP126.Interface.Solution.sphereH1_standard_class,
      ``KIP126.Interface.Solution.sphereH1_detects_eta,
      ``KIP126.Interface.Solution.sphereH1_eta_towerLift] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax || modelAxioms.contains ax do
        throwError "h1 producer adds an axiom beyond the fixed Def model: {decl}: {ax}"

#print axioms KIP126.LinE2.E2At_h1_eq_zero_or
#print axioms KIP126.Classical.Adams.MilnorCohomology.internal_hi_ne_zero
#print axioms KIP126.Interface.Solution.sphereH1_standard_class

#print axioms KIP126.Interface.Solution.sphereH1_eta_towerLift
