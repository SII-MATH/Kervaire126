module

public import KIP126.LinProgram.Certificates.RelationCatalogue
public import Lean
public meta import KIP126.LinProgram.Generated.E2

@[expose] public section


/-! Original-line membership certificates. Runtime selection proposes a
newline decomposition; Lean checks the decomposition and the generic proof. -/
namespace KIP126.LinE2.RelationCatalogue.Automation
open Lean Meta Elab Tactic
/-- Check membership of an exact raw line in an existing archived chunk. -/
syntax (name := linRelation) "lin_relation " num str : tactic

elab_rules : tactic
  | `(tactic| lin_relation $index:num $line:str) => withMainContext do
    let i := index.getNat
    unless i < RawData.relationChunks.size do
      throwError "lin_relation: chunk outside the archived data"
    let rows := RawData.relationChunks[i]!.splitOn "\n"
    let pos := rows.idxOf line.getString
    unless 0 < pos && pos + 1 < rows.length do
      throwError "lin_relation: expected an existing interior line"
    let cs := toExpr line.getString.toList
    let a := toExpr (String.intercalate "\n" (rows.take pos)).toList
    let b := toExpr (String.intercalate "\n" (rows.drop (pos + 1))).toList
    let ie := mkNatLit i
    let size ← mkAppM ``Array.size #[mkConst ``RawData.relationChunks]
    let hiType ← mkAppM ``LT.lt #[ie, size]
    let hi ← Term.elabTermEnsuringType (← `(by decide +kernel)) hiType
    let chunk ← Term.elabTerm
      (← `(KIP126.LinE2.RawData.relationChunks[$index]'(by decide +kernel))) none
    let charType := mkConst ``Char
    let cons (tail : Expr) := mkApp3 (mkConst ``List.cons [Level.zero]) charType
      (toExpr '\n') tail
    let append (xs ys : Expr) := mkApp3 (mkConst ``List.append [Level.zero]) charType xs ys
    let joined := append a (cons (append cs (cons b)))
    let hcType ← mkEq chunk (mkApp (mkConst ``String.ofList) joined)
    let hc ← Term.elabTermEnsuringType (← `(by rfl)) hcType
    let mem ← mkAppM ``Membership.mem #[cs, toExpr '\n']
    let hcsType := mkApp (mkConst ``Not) mem
    let hcs ← Term.elabTermEnsuringType (← `(by decide +kernel)) hcsType
    let proof ← mkAppM ``rawLine_mem_of_join #[ie, hi, a, cs, b, hc, hcs]
    unless ← isDefEq (← inferType proof) (← getMainTarget) do
      throwError "lin_relation: proposed archived line does not match the requested membership"
    (← getMainGoal).assign proof
    replaceMainGoal []

end KIP126.LinE2.RelationCatalogue.Automation
