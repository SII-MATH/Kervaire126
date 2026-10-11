module

public import KIP126.Interface.Solution.LinProgram.Naturality.Row245131Coordinates
public import Lean.Elab.Command

@[expose] public section


/-! The native data and literal coordinate certificates are closed, even
though the surrounding actual-model deliveries remain unfinished. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod ||
        mod == `KIP126.Interface.Solution.Challenge2 ||
        mod == `KIP126.Interface.Solution.LinProgram.Basis.Certification ||
        mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native coordinate certificate imported a delivery or assumed basis: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinE2.NaturalityCoordinates.sourceRow_mem,
      ``KIP126.LinE2.NaturalityCoordinates.targetRow_mem,
      ``KIP126.LinE2.NaturalityCoordinates.source_value,
      ``KIP126.LinE2.NaturalityCoordinates.target_value,
      ``KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.source_hasCoordinates,
      ``KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.target_hasCoordinates] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native naturality coordinate certificate {decl}: {ax}"

open KIP126.LinE2 in
example : True := by
  fail_if_success
    have : KIP126.Challenge2.HasCoordinates NaturalityCoordinates.source [] := by
      exact KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.source_hasCoordinates
  fail_if_success
    have : "5|19|1|0,1,8,1" ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n") := by
      lin_basis_line 0 "5|19|1|0,1,8,1"
  trivial

#print axioms KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.source_hasCoordinates
#print axioms KIP126.Interface.Solution.LinProgram.NaturalityCoordinates.target_hasCoordinates
