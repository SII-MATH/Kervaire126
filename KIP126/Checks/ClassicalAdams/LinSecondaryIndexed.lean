module

public import KIP126.LinProgram.Certificates.Secondary.IndexedExpansion
public import KIP126.LinProgram.Certificates.Secondary.Milnor.ProductTables
public import Lean.Elab.Command

@[expose] public section


namespace KIP126.Computation.Secondary.IndexedRegression
open MilnorCertificates

-- This entry carries an actual original-semantics product, not an assumed table value.
def testProducts (id : Nat) : Option ProductEntry :=
  if id = 0 then some ⟨[2],[1],[[3]]⟩ else none

def testImages (id : Nat) : Option ModuleExpression :=
  if id = 0 then some [⟨[1],3⟩] else none

theorem testProducts_sound (id : Nat) (entry : ProductEntry)
    (h : testProducts id = some entry) :
    IsMilnorProductAll 1 [entry.left] [entry.right] entry.output := by
  unfold testProducts at h
  split at h
  · cases h
    exact fastSingletonProductCheck_sound 1 [2] [1] [[3]] (by decide +kernel)
  · contradiction

theorem original_composition :
    compose 1 testImages [⟨[2],0⟩] =
      some (fun target m => expressionCoefficient [⟨[3],3⟩] target m.val) :=
  indexedCompositionCheck_sound 1 testProducts testImages [⟨[2],0⟩]
    [⟨0,3⟩] [⟨[3],3⟩] testProducts_sound (by decide +kernel)

-- Missing IDs/images and omitted/extra paths are rejected before cancellation.
example : indexedCompositionCheck testProducts testImages [⟨[2],0⟩] [] [] = false := by decide
example : indexedCompositionCheck testProducts testImages [⟨[2],0⟩] [⟨0,4⟩] [⟨[3],4⟩] = false := by decide
example : indexedCompositionCheck testProducts testImages [⟨[3],0⟩] [⟨0,3⟩] [⟨[3],3⟩] = false := by decide
example : indexedCompositionCheck testProducts testImages [⟨[2],0⟩] [⟨1,3⟩] [] = false := by decide
example : indexedCompositionCheck testProducts testImages [⟨[2],0⟩] [⟨0,3⟩,⟨0,3⟩] [] = false := by decide
example : indexedCompositionCheck testProducts testImages [⟨[2],1⟩,⟨[2],1⟩] [] [] = false := by decide
example : indexedExpansion testProducts [⟨1,3⟩,⟨1,3⟩] = none := by decide
example : fastExpressionEqCheck [⟨[1],3⟩,⟨[1],4⟩,⟨[1],3⟩] [⟨[1],4⟩] = true := by decide
example : fastExpressionEqCheck [⟨[1],3⟩] [⟨[1],4⟩] = false := by decide
example : fastExpressionEqCheck [⟨[1],3⟩] [⟨[2],3⟩] = false := by decide

-- The shared-table certificate includes every basis monomial of its exact degree.
def degreeThree : HomogeneousCoproductTable 2 3 where
  table := (degreeBasis 2 3).map fun m => (m, fastCoproduct 2 m)
  complete := rfl

example : degreeThree.table ≠ [] := by decide +kernel
example : fastSingletonProductCheckWithTable degreeThree [2,0] [1,0] [[3,0],[0,1]] = true := by decide +kernel
example : fastSingletonProductCheckWithTable degreeThree [2,0] [1,0] [[3,0]] = false := by decide +kernel
example : fastSingletonProductCheckWithTable degreeThree [1,0] [1,0] [] = false := by decide +kernel
example : fastSingletonProductCheckWithTable degreeThree [2] [1,0] [[3,0],[0,1]] = false := by decide +kernel

end KIP126.Computation.Secondary.IndexedRegression

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "indexed secondary checker imported an actual-model dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Secondary.fastSingletonProductCheckWithTable_sound,
      ``KIP126.Computation.Secondary.certifiedProductTable_sound,
      ``KIP126.Computation.Secondary.expressionCoefficient_perm,
      ``KIP126.Computation.Secondary.cancelAdjacent_sound,
      ``KIP126.Computation.Secondary.mergeExpression_perm,
      ``KIP126.Computation.Secondary.sortExpression_perm,
      ``KIP126.Computation.Secondary.normalizeExpression_sound,
      ``KIP126.Computation.Secondary.fastExpressionEqCheck_sound,
      ``KIP126.Computation.Secondary.indexedExpansion_sound,
      ``KIP126.Computation.Secondary.indexedCompositionCheck_sound,
      ``KIP126.Computation.Secondary.indexedExpansion_none_of_missing,
      ``KIP126.Computation.Secondary.IndexedRegression.testProducts_sound,
      ``KIP126.Computation.Secondary.IndexedRegression.original_composition] do
    for ax in ← collectAxioms decl do
      unless logical.contains ax do
        throwError "unexpected indexed secondary checker axiom {decl}: {ax}"
