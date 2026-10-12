module

import KIP126.Main.Solution.Route.Section7.ProofSupport

public import KIP126.Main.Solution.Route.AlphaOne
public import KIP126.Main.Solution.Route.Section7.Final

@[expose] public section

namespace KIP126.Main.Solution.Route.Section7
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Main.StageInput
noncomputable section

local notation "D" => routeModel
local notation "M" => standardMilnorCooperations
local notation "L" => routeLabels
local notation "I" => routeComputation
local notation "η" => routeEta
local notation "h₀" => routeLiterature.toda.h0



-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- Lemma `lem:toda2ext`, for all members of the stated bracket.
The independent weak-representative construction proves that C3 and C5
cannot hold together, so this conclusion follows with its original assumptions. -/
theorem main_toda_bracket_detected
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 11))
    (ha : AlphaOneProperties D η h₀ ((L).U M) eV a11) :
    let a9 := a11 ≫ ((D).quotientTower S_0_0).rho 9 11 (by decide)
    (∃ z : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h₀ η z) ∧
    (∀ z : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h₀ η z →
      FiniteDetected D 9 (by decide) 11 136 4 eY z) := by
  exact False.elim (c3_excludes_c5 hc3 hc5)

end
end KIP126.Main.Solution.Route.Section7
