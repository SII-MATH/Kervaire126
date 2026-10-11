module

public import KIP126.LinProgram.Certificates.Secondary.ModFour
public import Lean.Elab.Command

@[expose] public section


namespace KIP126.Computation.Secondary.ModFourRegression
open MilnorCertificates

-- The middle term 2*x ⊗ x survives modulo four; characteristic-two Frobenius
-- would erase it and give the wrong secondary half coefficient.
theorem retained_cross_term : singletonProductCoefficientMod4 1 [1] [1] [2] = 2 := by
  decide +kernel

theorem cross_term_mod_two_zero : pairTensor [[1]] [[1]] (coproduct 1 [2]) = false := by
  decide +kernel

theorem cross_term_half_nonzero : halveMod4 (singletonProductCoefficientMod4 1 [1] [1] [2]) =
    some true := by decide +kernel

def unitPath : CompositionPath := ⟨[0], [0], 7⟩

theorem two_paths_half_nonzero :
    halveMod4 (pathCoefficientMod4 1 7 [0] [unitPath, unitPath]) = some true := by
  decide +kernel

theorem four_paths_half_zero :
    halveMod4 (pathCoefficientMod4 1 7 [0] [unitPath, unitPath, unitPath, unitPath]) =
      some false := by decide +kernel

theorem odd_coefficient_rejected :
    halveMod4 (pathCoefficientMod4 1 7 [0] [unitPath, unitPath, unitPath]) = none := by
  decide +kernel

theorem unmatched_target_zero :
    pathCoefficientMod4 1 8 [0] [unitPath] = 0 := by decide +kernel

theorem malformed_residue_rejected : halveMod4 4 = none := by decide +kernel

-- Missing intermediate images still fail before any count or augmentation.
theorem missing_image_is_failure :
    compose 1 (fun _ => none) [⟨[0],7⟩,⟨[0],7⟩] = none := by decide +kernel

-- This complete original composition is zero, although the chosen lift has
-- nonzero half-coefficient. No invariance under F₂ normalization is asserted.
def duplicateImages (_ : Nat) : Option ModuleExpression := some [⟨[0],7⟩,⟨[0],7⟩]

theorem duplicate_composition_zero :
    compose 1 duplicateImages [⟨[0],0⟩] = some (fun _ _ => false) := by
  change some (fun target (m : {m : Monomial // m.length = 1}) =>
    pathCoefficient 1 target m.val [unitPath, unitPath]) = some (fun _ _ => false)
  congr 1
  funext target m
  simp [pathCoefficient]

theorem duplicate_composition_halves :
    ∃ paths, resolvePaths duplicateImages [⟨[0],0⟩] = some paths ∧
      ∀ target m, m.length = 1 →
        ∃ b, halveMod4 (pathCoefficientMod4 1 target m paths) = some b ∧
          pathCoefficientMod4 1 target m paths = 2 * b.toNat :=
  compose_zero_implies_mod4_halving 1 duplicateImages [⟨[0],0⟩] duplicate_composition_zero

end KIP126.Computation.Secondary.ModFourRegression

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "secondary mod-four imported an actual-model dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Secondary.singletonPairCount_parity,
      ``KIP126.Computation.Secondary.singletonProductCoefficientMod4_lt_four,
      ``KIP126.Computation.Secondary.singletonProductCoefficientMod4_mod_two,
      ``KIP126.Computation.Secondary.pathMultiplicity_parity,
      ``KIP126.Computation.Secondary.pathCoefficientMod4_lt_four,
      ``KIP126.Computation.Secondary.pathCoefficientMod4_cons,
      ``KIP126.Computation.Secondary.pathCoefficientMod4_mod_two,
      ``KIP126.Computation.Secondary.pathCoefficientMod4_zero_or_two,
      ``KIP126.Computation.Secondary.compose_zero_implies_mod4_two_torsion,
      ``KIP126.Computation.Secondary.halveMod4_eq_some_iff,
      ``KIP126.Computation.Secondary.halveMod4_exists_iff,
      ``KIP126.Computation.Secondary.halveMod4_path_of_zero,
      ``KIP126.Computation.Secondary.compose_zero_implies_mod4_halving,
      ``KIP126.Computation.Secondary.ModFourRegression.retained_cross_term,
      ``KIP126.Computation.Secondary.ModFourRegression.cross_term_mod_two_zero,
      ``KIP126.Computation.Secondary.ModFourRegression.cross_term_half_nonzero,
      ``KIP126.Computation.Secondary.ModFourRegression.two_paths_half_nonzero,
      ``KIP126.Computation.Secondary.ModFourRegression.four_paths_half_zero,
      ``KIP126.Computation.Secondary.ModFourRegression.odd_coefficient_rejected,
      ``KIP126.Computation.Secondary.ModFourRegression.unmatched_target_zero,
      ``KIP126.Computation.Secondary.ModFourRegression.malformed_residue_rejected,
      ``KIP126.Computation.Secondary.ModFourRegression.missing_image_is_failure,
      ``KIP126.Computation.Secondary.ModFourRegression.duplicate_composition_zero,
      ``KIP126.Computation.Secondary.ModFourRegression.duplicate_composition_halves] do
    for ax in ← collectAxioms decl do
      unless logical.contains ax do
        throwError "unexpected secondary mod-four axiom {decl}: {ax}"
