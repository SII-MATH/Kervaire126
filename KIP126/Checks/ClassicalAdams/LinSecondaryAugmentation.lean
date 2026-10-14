module

public import KIP126.LinProgram.Certificates.Secondary.Augmentation
public import Lean.Elab.Command

@[expose] public section


namespace KIP126.Computation.Secondary.AugmentationRegression
open MilnorCertificates

-- Missing nonunit paths must still fail even when their augmentation would vanish.
def missingImages (_ : Nat) : Option ModuleExpression := none

theorem missing_nonunit_is_failure :
    (compose 2 missingImages [⟨[1,0], 7⟩, ⟨[1,0], 7⟩]).map
      (fun f target => f target ⟨unitMonomial 2, by decide⟩) = none := by
  decide +kernel

-- A stored zero vector is different from the singleton coordinate numbered zero.
theorem singleton_zero_is_nonzero : augmentationCoefficient [0] 0 = true := by decide

theorem empty_is_zero (target : Nat) : augmentationCoefficient [] target = false := rfl

-- Raw unit occurrences retain parity rather than becoming set membership.
theorem duplicate_unit_cancels :
    expressionCoefficient [⟨[0,0], 7⟩, ⟨[0,0], 7⟩] 7 (unitMonomial 2) = false := by
  decide +kernel

end KIP126.Computation.Secondary.AugmentationRegression

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "secondary augmentation imported an actual-model dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Secondary.coproduct_unit,
      ``KIP126.Computation.Secondary.pairTensor_unit,
      ``KIP126.Computation.Secondary.product_augmentation,
      ``KIP126.Computation.Secondary.augmentationTerms_coefficient,
      ``KIP126.Computation.Secondary.pathCoefficient_unit,
      ``KIP126.Computation.Secondary.compose_augmentation,
      ``KIP126.Computation.Secondary.augmentation_eq_of_terms,
      ``KIP126.Computation.Secondary.AugmentationRegression.missing_nonunit_is_failure,
      ``KIP126.Computation.Secondary.AugmentationRegression.singleton_zero_is_nonzero,
      ``KIP126.Computation.Secondary.AugmentationRegression.empty_is_zero,
      ``KIP126.Computation.Secondary.AugmentationRegression.duplicate_unit_cancels] do
    for ax in ← collectAxioms decl do
      unless logical.contains ax do
        throwError "unexpected secondary augmentation axiom {decl}: {ax}"
