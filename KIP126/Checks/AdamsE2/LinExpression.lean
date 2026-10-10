import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Expressions.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Expressions.Predicates
import Lean.Elab.Command

/-! Executable migration regressions. Runtime checks are not proofs of the
CSV basis theorem or of Gröbner reduction soundness. -/
open KIP126.LinE2

#eval show IO Unit from do
  for (s, t, code) in [(1, 64, "69,1"), (2, 128, "69,2"), (0, 0, "")] do
    unless (decodeExpression s t code).isOk do
      throw (IO.userError s!"valid expression rejected: {code}")
  for (s, t, code) in [(1, 63, "69,1"), (2, 128, "2914,2"),
      (1, 1, "x,1"), (1, 1, "1"), (1, 1, "0,-1")] do
    if (decodeExpression s t code).isOk then
      throw (IO.userError s!"bad expression accepted: {code}")
  match parseBasisRows with
  | .error e => throw (IO.userError e)
  | .ok rows =>
    let mut counts : Std.HashMap (ℕ × ℕ) ℕ := {}
    for row in rows do
      unless (decodeExpression row.s row.t row.monomial).isOk do
        throw (IO.userError s!"basis degree mismatch: {repr row}")
      let key := (row.s, row.t)
      let next := (counts[key]?).getD 0
      unless row.index == next do
        throw (IO.userError "nonconsecutive CSV local index")
      counts := counts.insert key (next + 1)
  let .ok square := decodeExpression 2 128 "69,2"
    | throw (IO.userError "missing h6 square")
  let .ok cs := square.coordinates
    | throw (IO.userError "coordinate calculation failed")
  unless cs.map Fin.val == [0] do
    throw (IO.userError "h6 square has wrong basis address")
  if ((Expression.zero 0 262).coordinates).isOk then
    throw (IO.userError "out-of-range expression accepted")
  IO.println "Typed expressions: all CSV basis rows, h6 square coordinates and invalid inputs checked."

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``Expression.homogeneous, ``Expression.data_eq_interpret] do
    for a in (← liftCoreM (collectAxioms decl)) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected expression axiom: {decl}: {a}"
  let expected := logical ++ [``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation]
  for decl in [``KIP126.Classical.Adams.expressionOnSphere_mul,
      ``KIP126.Classical.Adams.expressionOnSphere_h6,
      ``KIP126.Classical.Adams.expressionOnSphere_h6_square] do
    discard <| KIP126.Checks.AxiomInputs.checkStageConsumer expected decl
      "unexpected sphere expression axiom"
  for m in (← getEnv).allImportedModuleNames do
    if (`KIPBase).isPrefixOf m || (`KIP126.Main.Challenge).isPrefixOf m then
      throwError "retired or placeholder import: {m}"
