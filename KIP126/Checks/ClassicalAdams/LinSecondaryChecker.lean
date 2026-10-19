module

public import KIP126.LinProgram.Certificates.Secondary.Expansion
public import KIP126.LinProgram.Certificates.Secondary.Milnor.Products
public import Lean.Elab.Command
public import KIP126.LinProgram.Certificates.Secondary.Seed5487.Data
public import KIP126.LinProgram.Certificates.Secondary.Seed5487.Products

@[expose] public section


namespace KIP126.Computation.Secondary.ExpansionRegression
open MilnorCertificates Seed5487

def products (left right : Monomial) : Option Polynomial :=
  if left = [0,0,1,0,0,0,0,0] ∧ right = [2,0,0,0,0,0,0,0] then
    some [[2,0,1,0,0,0,0,0]]
  else if left = [8,0,0,0,0,0,0,0] ∧ right = [1,0,0,0,0,0,0,0] then
    some [[6,1,0,0,0,0,0,0], [9,0,0,0,0,0,0,0]]
  else if left = [0,1,0,0,0,0,0,0] ∧ right = [1,0,0,0,0,0,0,0] then
    some [[1,1,0,0,0,0,0,0]]
  else if left = [2,0,0,0,0,0,0,0] ∧ right = [2,0,0,0,0,0,0,0] then
    some [[1,1,0,0,0,0,0,0]]
  else none

theorem products_sound (left right : Monomial) (product : Polynomial)
    (h : products left right = some product) : IsMilnorProductAll 8 [left] [right] product := by
  unfold products at h
  split_ifs at h with h₁ h₂ h₃ h₄
  · obtain ⟨rfl, rfl⟩ := h₁
    cases h
    exact product001_200_rank8
  · obtain ⟨rfl, rfl⟩ := h₂
    cases h
    exact product800_100_rank8
  · obtain ⟨rfl, rfl⟩ := h₃
    cases h
    exact product01_10_rank8
  · obtain ⟨rfl, rfl⟩ := h₄
    cases h
    exact product20_20_rank8

theorem row1572866_full_coefficients :
    compose 8 firstDifferentialImages row1572866.f =
      some (fun target m => expressionCoefficient row1572866.d_f target m.val) := by
  exact compositionCheck_sound 8 products firstDifferentialImages row1572866.f
    row1572866.d_f products_sound (by decide)

theorem row1048577_full_square_zero :
    compose 8 firstDifferentialImages row1048577.d = some (fun _ _ => false) := by
  simpa only [expressionCoefficient, List.filter_nil, List.map_nil, coefficient,
    List.length_nil, Nat.zero_mod, Nat.reduceBEq] using
    compositionCheck_sound 8 products firstDifferentialImages row1048577.d []
      products_sound (by decide)

/-- The same expected answer cannot certify the row when every product is missing. -/
example : compositionCheck (fun _ _ => none) firstDifferentialImages
    row1572866.f row1572866.d_f = false := by decide

/-- Duplicated targets cancel; another target is independent of the cancellation. -/
example : normalizationCheck [⟨[1,0],7⟩, ⟨[2,0],9⟩, ⟨[1,0],7⟩]
    [⟨[2,0],9⟩] = true := by decide

example : expressionEqCheck [⟨[2,0],9⟩] [⟨[2,0],8⟩] = false := by decide
example : expressionEqCheck [⟨[2,0],9⟩] [⟨[1,0],9⟩] = false := by decide
example : normalizationCheck [⟨[1,0],7⟩, ⟨[1,0],7⟩]
    [⟨[1,0],7⟩, ⟨[1,0],7⟩] = false := by decide

end KIP126.Computation.Secondary.ExpansionRegression

namespace KIP126.Computation.Secondary
-- Rank and complete output checks reject malformed or incomplete witnesses.
example : fastSingletonProductCheck 2 [2,0] [1,0] [[3,0],[0,1]] = true := by decide +kernel
example : fastSingletonProductCheck 2 [1,0] [2,0] [[3,0]] = true := by decide +kernel
example : fastSingletonProductCheck 2 [2,0] [1,0] [[3,0]] = false := by decide +kernel
example : fastSingletonProductCheck 2 [2] [1,0] [[3,0],[0,1]] = false := by decide +kernel
example : fastSingletonProductCheck 2 [2,0] [1,0] [[3],[0,1]] = false := by decide +kernel
example : fastSingletonProductCheck 2 [2,0] [1,0] [[3,0],[0,1],[4,0]] = false := by decide +kernel
example : fastSingletonProductCheck 8 [0,0,0,0,0,0,0,0] [0,0,0,0,0,0,0,0]
    [[0,0,0,0,0,0,0,0]] = true := by decide +kernel
example : (degreeBasis 8 40).length = 82 := by decide +kernel
end KIP126.Computation.Secondary

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod ||
        (`KIP126.Def).isPrefixOf mod then
      throwError "secondary checker imported an actual-model dependency: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Computation.Secondary.degreeBasis_mem,
      ``KIP126.Computation.Secondary.homogeneousProductCheck_sound,
      ``KIP126.Computation.Secondary.pairTensor_singletons_of_universal_eq,
      ``MilnorCertificates.squareTensor_arity, ``MilnorCertificates.tensorValue_square,
      ``MilnorCertificates.fastPower_arity, ``MilnorCertificates.tensorValue_fastPower,
      ``MilnorCertificates.fastCoproduct_arity, ``MilnorCertificates.fastCoproduct_value,
      ``KIP126.Computation.Secondary.pairTensor_fastCoproduct_singletons,
      ``KIP126.Computation.Secondary.fastSingletonProductCheck_sound,
      ``KIP126.Computation.Secondary.expressionCoefficient_append,
      ``KIP126.Computation.Secondary.expressionCoefficient_singleton,
      ``KIP126.Computation.Secondary.expressionCoefficient_cons,
      ``KIP126.Computation.Secondary.expressionCoefficient_duplicate_cancel,
      ``KIP126.Computation.Secondary.expressionCoefficient_of_not_mem,
      ``KIP126.Computation.Secondary.expressionEqCheck_sound,
      ``KIP126.Computation.Secondary.normalizationCheck_sound,
      ``KIP126.Computation.Secondary.expressionCoefficient_at_target,
      ``KIP126.Computation.Secondary.expandPaths_sound,
      ``KIP126.Computation.Secondary.expandPaths_none_of_missing,
      ``KIP126.Computation.Secondary.resolvePaths_none_of_missing,
      ``KIP126.Computation.Secondary.expandCompose_none_of_missing_image,
      ``KIP126.Computation.Secondary.expandCompose_none_of_missing_product,
      ``KIP126.Computation.Secondary.compose_of_expansion,
      ``KIP126.Computation.Secondary.compose_of_checked_expansion,
      ``KIP126.Computation.Secondary.compositionCheck_sound,
      ``KIP126.Computation.Secondary.ExpansionRegression.products_sound,
      ``KIP126.Computation.Secondary.ExpansionRegression.row1572866_full_coefficients,
      ``KIP126.Computation.Secondary.ExpansionRegression.row1048577_full_square_zero] do
    for ax in ← collectAxioms decl do
      unless logical.contains ax do
        throwError "unexpected secondary checker axiom {decl}: {ax}"
