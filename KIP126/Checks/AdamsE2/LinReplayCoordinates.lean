module

public import KIP126.LinProgram.Certificates.Products.Trial152097Coordinates
public import Lean.Elab.Command

@[expose] public section


/-! The typed native coordinate bridge must retain the closed data-algebra
trust boundary. Neither catalogue basis certification nor a model delivery
is a proof dependency. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        mod == `KIP126.LinProgram.Tactic.LinE2 then
      throwError "native coordinate certificate imported a model assumption: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.LinE2.ReplayCoordinates.sourceRow_mem,
      ``KIP126.LinE2.ReplayCoordinates.multiplierRow_mem,
      ``KIP126.LinE2.ReplayCoordinates.trialTargetRow_mem,
      ``KIP126.LinE2.ReplayCoordinates.productTargetRow_mem,
      ``KIP126.LinE2.ReplayCoordinates.source_value,
      ``KIP126.LinE2.ReplayCoordinates.multiplier_value,
      ``KIP126.LinE2.ReplayCoordinates.trialTarget_value,
      ``KIP126.LinE2.ReplayCoordinates.productTarget_value,
      ``KIP126.LinE2.ReplayCoordinates.source_mul_multiplier,
      ``KIP126.LinE2.ReplayCoordinates.multiplier_mul_trialTarget] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native coordinate certificate {decl}: {ax}"

open KIP126.LinE2 in
example : True := by
  fail_if_success
    have : (⟨4, 42, 0, "0,2,3,1,18,1"⟩ : BasisRow) = ReplayCoordinates.sourceRow := by
      decide
  fail_if_success
    have : mulAt dataH1 ReplayCoordinates.trialTarget = (0 : E2At 9 47) := by
      exact ReplayCoordinates.multiplier_mul_trialTarget
  trivial

#print axioms KIP126.LinE2.ReplayCoordinates.source_mul_multiplier
#print axioms KIP126.LinE2.ReplayCoordinates.multiplier_mul_trialTarget
