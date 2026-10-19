module

public import KIP126.Checks.AxiomInputs
public import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data
public import Lean.Elab.Command
public meta import KIP126.Checks.AxiomInputs

@[expose] public section

/-! The internal calculation must not obtain its sequence from a Mathlib adapter
or import the historical KIPBase component. -/
open Lean Elab Command in
run_cmd do
  for m in (← getEnv).allImportedModuleNames do
    if (`KIP126.Mathlib).isPrefixOf m || (`KIPBase).isPrefixOf m ||
        (`Mathlib.Algebra.Homology.SpectralSequence).isPrefixOf m then
      throwError "unexpected computational dependency: {m}"
  let env ← getEnv
  let model := ``KIP126.Classical.Adams.sphereAdamsModel
  let some (.defnInfo _) := env.find? model
    | throwError "the fixed sphere model must be a construction, not an axiom"
  for a in ← liftCoreM (collectAxioms model) do
    unless KIP126.Checks.AxiomInputs.allows [``propext, ``Classical.choice, ``Quot.sound,
        ``KIP126.Classical.Adams.standardFoundation] a do
      throwError "unexpected fixed sphere construction dependency: {a}"

example : KIP126.Classical.Adams.sphereAdamsData.r₀ = 2 :=
  KIP126.Classical.Adams.sphereAdamsModel.firstPage

example (r : ℤ) : KIP126.Classical.Adams.sphereAdamsData.diffDeg r = (r, r - 1) :=
  KIP126.Classical.Adams.sphereAdamsModel.differentialDegree r

open KIP126.Classical.Adams KIP126.StableHomotopy in
example : sphereAdamsData =
    adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum := rfl
