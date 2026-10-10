import KIP126.Checks.AxiomInputs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Selected.Proofs
import KIP126.Checks.ClassicalAdams.LinProofs

open Lean Elab Command in
run_cmd do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Core.SpectralSequence.RepresentsOnPage.eq_on_page_two,
      ``KIP126.Core.SpectralSequence.RepresentsOnPage.zero,
      ``KIP126.Core.SpectralSequence.HasNonzeroDifferential.toHasDifferential,
      ``KIP126.Core.SpectralSequence.HasDifferential.eq_on_page_two,
      ``KIP126.Core.SpectralSequence.hasDifferential_zero] do
    for a in (← liftCoreM (collectAxioms decl)) do
      unless KIP126.Checks.AxiomInputs.allows logical a do
        throwError "unexpected generic differential axiom: {decl}: {a}"
  let expected := [``propext, ``Classical.choice, ``Quot.sound,
    ``KIP126.Classical.Adams.standardFoundation,
    ``KIP126.Classical.Adams.linE2Presentation,
    ``KIP126.Computation.LinProofs.sphereTable_sound]
  for decl in [``KIP126.Computation.LinProofs.Selected.d2_x_125_8,
      ``KIP126.Computation.LinProofs.Selected.d2_h6,
      ``KIP126.Computation.LinProofs.Selected.d3_h4_x_109_12,
      ``KIP126.Computation.LinProofs.Selected.d3_h0Sq_x_123_13_2,
      ``KIP126.Computation.LinProofs.Selected.d3_x_126_4,
      ``KIP126.Computation.LinProofs.Selected.d7_x_123_11_combination] do
    let axioms ← KIP126.Checks.AxiomInputs.checkStageConsumer expected decl
      "selected-result dependency audit"
    unless KIP126.Checks.AxiomInputs.uses axioms
        ``KIP126.Computation.LinProofs.sphereTable_sound do
      throwError "missing Challenge 2 database assumption: {decl}"

open KIP126.Core KIP126.Core.SpectralSequence
open CategoryTheory

example {R : Type} [Ring R] (E : SpectralSequence (ModuleCat R) (ℤ × ℤ))
    (p : ℤ × ℤ) {x y : E.Page 2 p} (h : RepresentsOnPage E 2 p x y) :
    x = y := h.eq_on_page_two

example {R : Type} [Ring R] (E : SpectralSequence (ModuleCat R) (ℤ × ℤ))
    (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    HasDifferential E r p (p + E.diffDeg r) 0 0 := hasDifferential_zero hr rfl

example {R : Type} [Ring R] (E : SpectralSequence (ModuleCat R) (ℤ × ℤ))
    (r : ℤ) (p q : ℤ × ℤ) (hdeg : p + E.diffDeg r ≠ q)
    (x : E.Page 2 p) (y : E.Page 2 q) : ¬ HasDifferential E r p q x y :=
  fun h => hdeg h.target_degree
