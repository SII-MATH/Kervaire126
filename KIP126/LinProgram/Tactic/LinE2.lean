import KIP126.LinProgram.Tactic.Support.Proofs
import Lean

/-! PR #110 concrete E₂ tactic. Successful proofs still use the explicitly
unfinished `coordinateCheck_sound`; this is not certified normalization.
On Lean 4.32, `native_decide` also emits a fresh evaluation axiom at each use.
The strict project audit intentionally rejects these; it is not weakened here.
Replacing native evaluation by kernel-checked certificates is separate debt. -/
namespace KIP126.LinE2.Automation
open Compute

open Lean Meta Elab Tactic

private def codeExpr : Code → Expr
  | .scalar n => mkApp (mkConst ``Code.scalar) (mkNatLit n)
  | .gen n => mkApp (mkConst ``Code.gen) (mkNatLit n)
  | .add a b => mkApp2 (mkConst ``Code.add) (codeExpr a) (codeExpr b)
  | .mul a b => mkApp2 (mkConst ``Code.mul) (codeExpr a) (codeExpr b)
  | .pow a n => mkApp2 (mkConst ``Code.pow) (codeExpr a) (mkNatLit n)

private def concreteNat (e : Expr) : MetaM Nat := do
  let e ← whnf e
  let some n ← (evalNat e).run | throwError "e2_mul: expected a concrete natural number, got {e}"
  return n

/-- 不把未知变量当作生成元；仅展开闭合的命名常量和局部 let。 -/
private def reify : Nat → Expr → MetaM Code
  | 0, e => throwError "e2_mul: expression unfolding limit reached at {e}"
  | n + 1, original => do
    let e ← instantiateMVars original
    let e := e.consumeMData
    let args := e.getAppArgs
    if e.isAppOfArity ``generator 1 then
      let value ← mkAppM ``Fin.val #[args[0]!]
      return .gen (← concreteNat value)
    if e.isAppOfArity ``OfNat.ofNat 3 then
      return .scalar (← concreteNat args[1]!)
    if e.isAppOfArity ``HAdd.hAdd 6 then
      return .add (← reify n args[4]!) (← reify n args[5]!)
    if e.isAppOfArity ``HMul.hMul 6 then
      return .mul (← reify n args[4]!) (← reify n args[5]!)
    if e.isAppOfArity ``HPow.hPow 6 then
      return .pow (← reify n args[4]!) (← concreteNat args[5]!)
    if let .letE _ _ value body _ := e then
      return ← reify n (body.instantiate1 value)
    if let .fvar f := e then
      let decl ← f.getDecl
      if let some value := decl.value? then return ← reify n value
      throwError "e2_mul: {e} is an unknown element; provide a concrete generator/basis expression"
    if let some unfolded ← unfoldDefinition? e then
      return ← reify n unfolded
    throwError "e2_mul: unsupported concrete E2 expression: {e}"

initialize engineCache : IO.Ref (Option Engine) ← IO.mkRef none

private def getEngine : TacticM Engine := do
  if let some e ← engineCache.get then return e
  logInfo "e2_mul: initializing the complete CSV relation and basis indices…"
  match loadEngine with
  | .error msg => throwError "e2_mul: data initialization failed: {msg}"
  | .ok e => engineCache.set (some e); return e

/-- 使用方式：`by e2_mul` 或 `by e2_mul 2000000`（约化步数上限）。 -/
syntax (name := e2Mul) "e2_mul" (num)? : tactic

elab_rules : tactic
  | `(tactic| e2_mul $[$limit:num]?) => withMainContext do
    let fuel := limit.map (·.getNat) |>.getD 1000000
    let goal ← getMainGoal
    let target ← whnf (← instantiateMVars (← goal.getType))
    let some (ty, lhs, rhs) := target.consumeMData.eq? |
      throwError "e2_mul: expected an equality of concrete E2 elements"
    unless ← isDefEq ty (mkConst ``E2) do
      throwError "e2_mul: expected KIP126.LinE2.E2, got {ty}"
    let a ← reify 256 lhs
    let b ← reify 256 rhs
    let ae := codeExpr a
    let be := codeExpr b
    unless ← isDefEq lhs (mkApp (mkConst ``interpret) ae) do
      throwError "e2_mul: left-hand expression does not match its reification"
    unless ← isDefEq rhs (mkApp (mkConst ``interpret) be) do
      throwError "e2_mul: right-hand expression does not match its reification"
    let e ← getEngine
    let lc ← match coordinates e a fuel with
      | .ok c => pure c
      | .error msg => throwError "e2_mul: left-hand computation failed: {msg}"
    let rc ← match coordinates e b fuel with
      | .ok c => pure c
      | .error msg => throwError "e2_mul: right-hand computation failed: {msg}"
    unless lc == rc do
      throwError "e2_mul: CSV basis coordinates differ\nleft: {repr lc}\nright: {repr rc}"
    let check := mkApp3 (mkConst ``coordinateCheck) ae be (mkNatLit fuel)
    let checkType ← mkEq check (mkConst ``Bool.true)
    let cert ← Term.elabTermEnsuringType (← `(by native_decide)) checkType
    let proof ← mkAppM ``coordinateCheck_sound #[ae, be, mkNatLit fuel, cert]
    goal.assign proof
    replaceMainGoal []
    logWarning "e2_mul: coordinates checked; proof uses admitted coordinateCheck_sound (sorryAx) and a native_decide evaluation axiom."

end KIP126.LinE2.Automation
