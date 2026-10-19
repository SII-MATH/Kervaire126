module

public import KIP126.LinProgram.Certificates.BranchD2Coordinates
public import Lean.Elab.Command

import all Init.Data.List.SplitOn.Basic
import all Init.Data.Repr

@[expose] public section


/-! Independent native finite matrix certificates, without a sphere/CW page
comparison, total computation result, or candidate-coverage assumption. -/
open KIP126.LinProgram.BranchD2Coordinates

attribute [local cbv_eval] KIP126.LinE2.SquareDetection.splitOn_comma
  KIP126.LinE2.SquareDetection.toNat?_eq_chars Nat.repr_eq_ofList_toDigits

example : decodeColumn 4 none = .error (.coordinate .sqlNull) := by rfl
example : decodeColumn 4 (some "-1") = .error (.coordinate (.unknown "-1")) := by cbv
example : decodeColumn 4 (some "[NULL]") = .error (.coordinate (.unknown "[NULL]")) := by cbv
example : decodeColumn 4 (some "01") = .error (.coordinate (.malformed "01")) := by cbv
example : decodeColumn 4 (some "1,1") = .error .notIncreasing := by cbv
example : decodeColumn 4 (some "3,1") = .error .notIncreasing := by cbv
example : decodeColumn 4 (some "4") = .error .outOfRange := by cbv
example : decodeMatrix 4 5 [some "1,3", some "", some "", some ""] =
    .error .columnCount := by cbv
example : decodeMatrix 4 5 [some "1,3", some "", some "", some "", none] =
    .error (.coordinate .sqlNull) := by cbv

/-- The repeated outgoing column matters; it is not dropped as a zero. -/
example : outgoing ![0, 0, 0, 1] ≠ 0 := by decide +kernel
example : boundary ∈ LinearMap.ker outgoing := by rw [kernel_iff]; rfl
example : representative 1 ∈ LinearMap.ker outgoing := representative_mem_kernel 1
example : representative 1 ∉ LinearMap.range incoming := by
  rw [image_iff]
  decide +kernel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "native matrix certificate imports actual delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``incoming_decoded, ``outgoing_decoded, ``incoming_apply,
      ``outgoing_apply, ``kernel_iff, ``image_iff, ``image_le_kernel,
      ``representatives_decoded, ``representative_mem_kernel,
      ``kernel_mod_image_representatives] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in full native matrix certificate {decl}: {ax}"

#print axioms kernel_mod_image_representatives
