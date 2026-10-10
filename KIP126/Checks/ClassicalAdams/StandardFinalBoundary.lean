import KIP126.Main.Challenge.h6_sq_permanent
import Lean.Elab.Command

/-! Inspect the standard target in isolation: C(M) may be used by its eventual
proof, but must not enter the target's objects or statement. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126).isPrefixOf m &&
        !(`KIP126.Def).isPrefixOf m &&
        m != `KIP126.Main.Challenge.h6_sq_permanent then
      throwError "T(M) has a non-Def project import: {m}"
  let target := ``KIP126.Challenge.Final.H6SquarePermanent.h6_sq_permanent
  let some (.thmInfo ti) := env.find? target | throwError "missing standard target"
  unless ti.type.getUsedConstants.contains ``KIP126.Classical.Adams.standardH6Square &&
      ti.type.getUsedConstants.contains ``KIP126.Core.SpectralSequence.NonzeroSurvival do
    throwError "T(M) must refer to standard h6 square and internal nonzero survival"
  unless ti.value.getUsedConstants.contains ``sorryAx do
    throwError "Challenge must remain a statement placeholder"
  -- Traverse the entire defining cone of the TYPE. Foundational construction
  -- proofs may still contain sorryAx at stage 0; no stage axiom, C/A object,
  -- or intentionally unfinished Challenge theorem may define the target.
  let mut todo := ti.type.getUsedConstants
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "missing target dependency: {name}"
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if (`KIP126).isPrefixOf owner then
        unless (`KIP126.Def).isPrefixOf owner do
          throwError "T(M)'s defining constant is outside Def: {name}: {owner}"
        if (`KIP126.Def.Challenge).isPrefixOf owner then
          throwError "T(M) depends on a statement-only placeholder: {name}"
        if let .axiomInfo _ := info then
          throwError "T(M) depends on a project axiom: {name}"
      else continue
    todo := todo ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then todo := todo ++ value.getUsedConstants

open KIP126.Classical.Adams KIP126.StableHomotopy

-- Scope changes to Challenge2 must not weaken the fixed standard h₆² goal.
open KIP126.Core.SpectralSequence in
example : NonzeroSurvival sphereAdamsData (2, 128) standardH6Square :=
  KIP126.Challenge.Final.H6SquarePermanent.h6_sq_permanent

example : sphereAdamsData =
    adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum := rfl

example : standardH6Square =
    Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 6 := rfl

example : sphereAdamsData.r₀ = 2 := rfl

example (r : ℤ) : sphereAdamsData.diffDeg r = (r, r - 1) := rfl
