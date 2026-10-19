module

public import KIP126.Def.SpectralSequence.Computation.PageThree.Proofs
public import Lean.Elab.Command

@[expose] public section


/-! Full-scope third-page calculus and its transitive trust boundary. -/
open CategoryTheory KIP126.Core KIP126.Core.SpectralSequence
universe u v
variable {R : Type u} [Ring R]
variable (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))

example (p : ℤ × ℤ) (y : E.Page 3 p) :
    ∃ x : E.Page 2 p, RepresentsOnPage E 3 p x y :=
  PageThree.exists_representative p y

example (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ) (x : E.Page 2 p) :
    ReachesPage E 3 p x ↔ E.d 2 p x = 0 :=
  PageThree.reachesPage_iff_d2_eq_zero hstart p x

example (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    (x : E.Page 2 (p + E.diffDeg 2)) :
    IsBoundaryBy E 2 (p + E.diffDeg 2) x ↔
      ∃ z : E.Page 2 p, E.d 2 p z = x :=
  PageThree.isBoundaryBy_iff_mem_d2_range hstart p x

example (hstart : E.r₀ ≤ 2) (p : ℤ × ℤ)
    {a b : E.Page 2 (p + E.diffDeg 2)} {x y : E.Page 3 (p + E.diffDeg 2)}
    (ha : RepresentsOnPage E 3 (p + E.diffDeg 2) a x)
    (hb : RepresentsOnPage E 3 (p + E.diffDeg 2) b y) :
    x = y ↔ ∃ z : E.Page 2 p, E.d 2 p z = a - b :=
  PageThree.equal_iff_sub_mem_d2_range hstart p ha hb

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.LinProgram).isPrefixOf mod then
      throwError "generic third-page calculus imports a delivery or fixed artifact: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``PageThree.exists_representative,
      ``PageThree.reachesPage_iff_d2_eq_zero,
      ``PageThree.isBoundaryBy_iff_mem_d2_range,
      ``PageThree.represents_iff_sub_mem_d2_range,
      ``PageThree.equal_iff_sub_mem_d2_range] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in generic third-page calculus {decl}: {ax}"

#print axioms PageThree.exists_representative
#print axioms PageThree.reachesPage_iff_d2_eq_zero
#print axioms PageThree.represents_iff_sub_mem_d2_range
