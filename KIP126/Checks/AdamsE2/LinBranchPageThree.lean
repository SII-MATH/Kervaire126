module

public import KIP126.LinProgram.Certificates.BranchPageThree
public import Lean.Elab.Command

@[expose] public section


/-! The matrix transport retains every third-page element, every input vector
in both squares, and full E₂ coordinate isomorphisms. -/
open CategoryTheory KIP126.Core KIP126.Core.SpectralSequence
open KIP126.LinProgram.BranchD2Coordinates
universe v

example (E : SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)) (hstart : E.r₀ ≤ 2)
    (p : ℤ × ℤ)
    (eIncoming : Coordinates 5 ≃ₗ[ℤ] E.Page 2 p)
    (eMiddle : Coordinates 4 ≃ₗ[ℤ] E.Page 2 (p + E.diffDeg 2))
    (eOutgoing : Coordinates 4 ≃ₗ[ℤ] E.Page 2 ((p + E.diffDeg 2) + E.diffDeg 2))
    (incoming_commutes : ∀ v : Coordinates 5,
      E.d 2 p (eIncoming v) = eMiddle (incoming v))
    (outgoing_commutes : ∀ v : Coordinates 4,
      E.d 2 (p + E.diffDeg 2) (eMiddle v) = eOutgoing (outgoing v)) :
    ∀ y : E.Page 3 (p + E.diffDeg 2), ∃! i : Fin 4,
      RepresentsOnPage E 3 (p + E.diffDeg 2) (eMiddle (representative i)) y :=
  KIP126.LinProgram.BranchPageThree.representatives E hstart p
    eIncoming eMiddle eOutgoing incoming_commutes outgoing_commutes

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "conditional native E3 transport imports an actual delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in (← collectAxioms ``KIP126.LinProgram.BranchPageThree.representatives) do
    unless logical.contains ax do
      throwError "unexpected axiom in conditional native E3 transport: {ax}"

#print axioms KIP126.LinProgram.BranchPageThree.representatives
