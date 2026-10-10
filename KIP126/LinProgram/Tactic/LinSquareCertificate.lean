import KIP126.LinProgram.Certificates.SquareDetection.Certificate
import Lean

/-! Kernel-checked certificates for the archived nonzero-square detector.

Native execution only proposes character lists and a proof tree. Every leaf
uses `decide +kernel`, every join uses a proved generic lemma, and the final
proof must match the original archived strings by definitional equality.
No `native_decide`, evaluation axiom, unchecked declaration, or dataset
replacement is used. Auxiliary declarations are checked synchronously to
bound the queue of pending kernel tasks. -/

namespace KIP126.LinE2.SquareDetection.Automation

open Lean Meta Elab Tactic

private def saveCertificate (cs proof : Expr) : TermElabM Expr := do
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars proof
  let type ← mkEq (mkApp (mkConst ``charsChunkCheck) cs) (mkConst ``Bool.true)
  let name ← mkAuxDeclName `squareCertificate
  withOptions (fun opts => opts.setBool `Elab.async false) do
    addDecl (.thmDecl { name, levelParams := [], type, value })
  return mkConst name

private partial def certifyRows (rows : List String) : TermElabM (Expr × Expr) := do
  let cs := toExpr (String.intercalate "\n" rows).toList
  let proof ← if rows.length > 8 then do
    let (a, pa) ← certifyRows (rows.take (rows.length / 2))
    let (b, pb) ← certifyRows (rows.drop (rows.length / 2))
    pure <| mkAppN (mkConst ``charsChunkCheck_append) #[a, b, pa, pb]
  else do
    let type ← mkEq (mkApp (mkConst ``charsChunkCheck) cs) (mkConst ``Bool.true)
    Term.elabTermEnsuringType (← `(by decide +kernel)) type
  return (cs, ← saveCertificate cs proof)

/-- Prove `chunksCheck ((RawData.relationChunks.toList.drop start).take count) = true`.
The numeric arguments select existing data; they do not add hypotheses. -/
syntax (name := linSquareChunks) "lin_square_chunks " num num : tactic

elab_rules : tactic
  | `(tactic| lin_square_chunks $first:num $count:num) => withMainContext do
    let first := first.getNat
    let count := count.getNat
    unless 0 < count && first + count ≤ RawData.relationChunks.size do
      throwError "lin_square_chunks: expected a nonempty range inside the archived chunks"
    let chunks := (RawData.relationChunks.toList.drop first).take count
    let mut certificates := #[]
    for s in chunks do
      let (cs, proof) ← certifyRows (s.splitOn "\n")
      certificates := certificates.push
        (mkStrLit s, mkApp2 (mkConst ``charsChunkCheck_ofList) cs proof)
    let mut tail := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``String)
    let mut proof := mkConst ``chunksCheck_nil
    for (s, hs) in certificates.reverse do
      proof := mkAppN (mkConst ``chunksCheck_cons) #[s, tail, hs, proof]
      tail := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``String) s tail
    (← getMainGoal).assign proof
    replaceMainGoal []

/-- Join already checked chunk certificates without rerunning their Boolean checks.
Keeping each archived chunk in its own theorem bounds elaboration work per
declaration at the ordinary heartbeat limit. -/
syntax (name := linSquareCompose) "lin_square_compose " ident+ : tactic

elab_rules : tactic
  | `(tactic| lin_square_compose $names:ident*) => withMainContext do
    let mut xs := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``String)
    let mut proof := mkConst ``chunksCheck_nil
    for id in names.reverse do
      let name ← realizeGlobalConstNoOverloadWithInfo id
      let type := (← getConstInfo name).type
      let some (_, lhs, _) := type.eq? | throwError "expected a chunk certificate"
      unless lhs.isAppOf ``chunksCheck do
        throwError "expected a chunksCheck equality"
      let ys := lhs.appArg!
      proof := mkAppN (mkConst ``chunksCheck_append) #[ys, xs, mkConst name, proof]
      xs := mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``String) ys xs
    (← getMainGoal).assign proof
    replaceMainGoal []

end KIP126.LinE2.SquareDetection.Automation
