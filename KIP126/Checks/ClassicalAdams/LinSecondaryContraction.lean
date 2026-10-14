module

public import KIP126.LinProgram.Certificates.Secondary.Contraction
public import Lean.Elab.Command

@[expose] public section


namespace KIP126.Computation.Secondary.ContractionRegression
open MilnorCertificates

-- Powers subtract when there are enough copies, even when the tested binary bit is zero.
theorem coordinate_subtraction :
    contractMonomial [0,2,0] [1,4,0] = some [1,2,0] := by decide +kernel

theorem underflow_is_zero : contractMonomial [0,4,0] [1,3,0] = none := by decide +kernel

theorem short_rank_rejected : contractMonomial [0,0] [1] = none := by decide +kernel

theorem long_rank_rejected : contractMonomial [0] [1,0] = none := by decide +kernel

theorem rank_zero_identity : contractMonomial [] [] = some [] := rfl

theorem xi_zero_identity : contractPolynomial (generatorPower 3 0 16) [[2,1,0]] =
    [[2,1,0]] := by decide +kernel

-- Duplicate terms remain two occurrences; their coefficients cancel in F₂.
theorem contraction_preserves_multiplicity :
    contractPolynomial [1,0] [[2,0],[0,1],[2,0]] = [[1,0],[1,0]] := by decide +kernel

theorem contracted_duplicates_cancel :
    coefficient (contractPolynomial [1,0] [[2,0],[0,1],[2,0]]) [1,0] = false := by
  decide +kernel

theorem target_preserved :
    contractModuleExpression [1,0] [⟨[2,0],7⟩,⟨[0,1],9⟩,⟨[3,0],8⟩] =
      [⟨[1,0],7⟩,⟨[2,0],8⟩] := by decide +kernel

-- The support bound is a general theorem at the full original rank.
theorem outer_index_impossible (q : Monomial) (hq : weight q < 32) :
    contractMonomial (generatorPower 8 (6-2) (2^2)) q = none :=
  outerContraction_eq_none_of_weight_lt 8 6 2 q (by decide) (by decide) hq

end KIP126.Computation.Secondary.ContractionRegression

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "secondary contraction imported an actual-model dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Secondary.contractMonomial_eq_some,
      ``KIP126.Computation.Secondary.contractMonomial_length,
      ``KIP126.Computation.Secondary.contractMonomial_eq_none_of_length_ne,
      ``KIP126.Computation.Secondary.contractMonomial_eq_none_iff,
      ``KIP126.Computation.Secondary.coefficient_cons,
      ``KIP126.Computation.Secondary.contractPolynomial_coefficient,
      ``KIP126.Computation.Secondary.multiplyMonomial_comm,
      ``KIP126.Computation.Secondary.multiplyMonomial_assoc,
      ``KIP126.Computation.Secondary.contractPolynomial_twice_coefficient,
      ``KIP126.Computation.Secondary.contractPolynomial_xi_zero_coefficient,
      ``KIP126.Computation.Secondary.contractPolynomial_generatorPower_coefficient,
      ``KIP126.Computation.Secondary.contractModuleExpression_coefficient,
      ``KIP126.Computation.Secondary.contractMonomial_weight,
      ``KIP126.Computation.Secondary.contractMonomial_eq_none_of_weight_lt,
      ``KIP126.Computation.Secondary.contractGeneratorPower_eq_none_of_weight_lt,
      ``KIP126.Computation.Secondary.outerContraction_factor_weight_lower,
      ``KIP126.Computation.Secondary.outerContraction_eq_none_of_weight_lt,
      ``KIP126.Computation.Secondary.ContractionRegression.coordinate_subtraction,
      ``KIP126.Computation.Secondary.ContractionRegression.underflow_is_zero,
      ``KIP126.Computation.Secondary.ContractionRegression.short_rank_rejected,
      ``KIP126.Computation.Secondary.ContractionRegression.long_rank_rejected,
      ``KIP126.Computation.Secondary.ContractionRegression.rank_zero_identity,
      ``KIP126.Computation.Secondary.ContractionRegression.xi_zero_identity,
      ``KIP126.Computation.Secondary.ContractionRegression.contraction_preserves_multiplicity,
      ``KIP126.Computation.Secondary.ContractionRegression.contracted_duplicates_cancel,
      ``KIP126.Computation.Secondary.ContractionRegression.target_preserved,
      ``KIP126.Computation.Secondary.ContractionRegression.outer_index_impossible] do
    for ax in ← collectAxioms decl do
      unless logical.contains ax do
        throwError "unexpected secondary contraction axiom {decl}: {ax}"
