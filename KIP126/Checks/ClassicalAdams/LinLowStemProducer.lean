module

public import KIP126.Interface.Solution.LinProgram.Differentials.VanishingD2
public import Lean.Elab.Command
public import KIP126.LinProgram.Tactic.LinBasisLine

@[expose] public section


/-! Audit the producer, independently of Main's temporary Challenge2 witness.
The fixed Def model still has admitted construction dependencies; those are
reported explicitly and are not proof-completion evidence. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod ||
        mod == `KIP126.Interface.Solution.Challenge2 ||
        mod == `KIP126.Interface.Solution.LinProgram.Basis.Certification then
      throwError "low-stem producer imported a consumer or admitted certificate: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Core.SpectralSequence.RepresentsOnPage.self_two,
      ``KIP126.Core.SpectralSequence.hasDifferential_two_of_subsingleton_target,
      ``KIP126.LinE2.BasisCatalogue.archivedChunks_valid,
      ``KIP126.LinE2.LowStem.ph1Row_mem,
      ``KIP126.LinE2.LowStem.ph1_value] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in independent certificate {decl}: {ax}"
  let modelAxioms ← collectAxioms ``KIP126.Classical.Adams.sphereAdamsModel
  for decl in [``KIP126.Interface.Solution.LinProgram.d2_zero_of_vanishingLine,
      ``KIP126.Interface.Solution.LinProgram.row5432] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax || modelAxioms.contains ax do
        throwError "producer adds an axiom beyond the fixed Def model: {decl}: {ax}"

set_option maxRecDepth 2048 in
example : KIP126.Computation.LinProofs.RawData.lookup 0 0 =
    some ⟨5432, "d2", 5, 14, 2, [0], []⟩ := rfl

/-- A changed local coordinate is absent from the raw CSV and must be rejected. -/
example : True := by
  fail_if_success
    have h : "5|14|1|5,1" ∈ KIP126.LinE2.RawData.basisChunks.toList.flatMap
        (·.splitOn "\n") := by
      lin_basis_line 0 "5|14|1|5,1"
  trivial

#print axioms KIP126.LinE2.LowStem.ph1Row_mem
#print axioms KIP126.Interface.Solution.LinProgram.row5432
