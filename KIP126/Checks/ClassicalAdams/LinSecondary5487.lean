module

public import KIP126.LinProgram.Certificates.Secondary.Seed5487.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! Closed algebra identities from the same native seed5487 closure. The audit
rejects an actual-model delivery, an admitted proof, or a new project axiom. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "finite secondary certificate imported an actual-model dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Secondary.Seed5487.row1048577_d_squared,
      ``KIP126.Computation.Secondary.Seed5487.row1572866_d_f,
      ``KIP126.Computation.Secondary.Seed5487.row3145729_d_f,
      ``MilnorCertificates.checkAll_sound, ``MilnorCertificates.stable_product] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in finite secondary certificate {decl}: {ax}"

namespace KIP126.Computation.Secondary.Seed5487
open MilnorCertificates

-- Missing native images must not silently become zero differential columns.
example : compose 8 (fun _ => none) row1048577.d = none := rfl

-- Deleting the second actual path destroys the cancellation.
example : compose 8 firstDifferentialImages [⟨[0,1,0,0,0,0,0,0],0⟩] ≠
    some (fun _ _ => false) := by
  intro h
  have h0 := congrArg
    (fun value => value.map fun f => f 0 ⟨[1,1,0,0,0,0,0,0],rfl⟩) h
  change some (xor
    (pairTensor [[0,1,0,0,0,0,0,0]] [[1,0,0,0,0,0,0,0]]
      (coproduct 8 [1,1,0,0,0,0,0,0])) false) = some false at h0
  rw [Bool.xor_false,
    ← product01_10_rank8.2.2.2 [1,1,0,0,0,0,0,0] rfl] at h0
  have ht : coefficient [[1,1,0,0,0,0,0,0]] [1,1,0,0,0,0,0,0] = true := by decide
  rw [ht] at h0
  contradiction

-- A changed output is rejected by the reused semantic checker.
example : checkAll 2 [[0,1]] [[1,0]] [] ⟨generate ⟨2,4⟩,3,1⟩ = false := by decide

-- This new path also rejects an absent native differential image.
example : compose 8 (fun _ => none) row3145729.f = none := rfl

-- Deleting the second output term changes the actual composite coefficient.
example : compose 8 fourthDifferentialImages row3145729.f ≠
    some (fun target m => expressionCoefficient
      [⟨[2,1,1,0,0,0,0,0],0⟩] target m.val) := by
  rw [row3145729_d_f]
  intro h
  have h0 := congrArg
    (fun value => value.map fun f => f 0 ⟨[5,0,1,0,0,0,0,0],rfl⟩) h
  change some true = some false at h0
  contradiction

end KIP126.Computation.Secondary.Seed5487

#print axioms KIP126.Computation.Secondary.Seed5487.row1048577_d_squared
#print axioms KIP126.Computation.Secondary.Seed5487.row1572866_d_f

#print axioms KIP126.Computation.Secondary.Seed5487.row3145729_d_f
