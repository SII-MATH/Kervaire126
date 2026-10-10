import Lean.Elab.Command

/-! Contract types may be imported from Interface/Challenge. Main's intentional
final-goal placeholder may never establish a Solution theorem. -/
namespace KIP126.Checks
open Lean Elab Command

def rejectGoalProofs (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      -- Declaration namespaces may differ from their source module names.
      if (`KIP126.Main.Challenge).isPrefixOf owner ||
          (`KIP126.Def.Challenge).isPrefixOf owner then
        throwError "Solution depends on an intentional goal proof: {name}: {owner}"
      unless (`KIP126).isPrefixOf owner do continue
    pending := pending ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants

end KIP126.Checks
