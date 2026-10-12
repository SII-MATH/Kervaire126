module

import KIP126.Main.Solution.Route.Section7.ProofSupport

public import KIP126.Main.Solution.Route.Section7.Common
import KIP126.Main.Solution.Computation.LowDegrees
import KIP126.Main.Solution.Route.Section7.ThetaToda
import KIP126.Main.Solution.Route.Section7.ThetaShuffle
import KIP126.Main.Solution.Route.AlphaOne
import Batteries.Tactic.OpenPrivate

-- Internal M16 implementation; downstream milestones import only this module.
import all KIP126.Main.Solution.Route.Section7.AnyYHelpers
import all KIP126.Main.Solution.Route.Section7.TodaNonempty
import all KIP126.Main.Solution.Route.Section7.WeakInitialNonzero
import all KIP126.Main.Solution.Route.Section7.WeakRepresentative
import all KIP126.Main.Solution.Route.Section7.WeakYDetection

public section

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

attribute [local irreducible] KIP126.LinE2.homogeneousPart

open private anyy_eta_unique_from_low_degrees anyy_bracket_exact_target
  from KIP126.Main.Solution.Route.Section7.AnyYHelpers
open private main_module_toda_nonempty_of_alpha
  from KIP126.Main.Solution.Route.Section7.TodaNonempty
open private weak_initial_twice_h0_nonzero
  from KIP126.Main.Solution.Route.Section7.WeakInitialNonzero
open private main_weak_high_representative
  from KIP126.Main.Solution.Route.Section7.WeakRepresentative
open private weak_y_detected_from_low
  from KIP126.Main.Solution.Route.Section7.WeakYDetection

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- M16 public handoff on the sole fixed `Challenge2` witness: one and the
same representative is detected by `λ⁴Y` in the ninth quotient and retains
its nonzero `λ²h₀` product. Its construction does not use the final contradiction.
The input's unfinished foundation and certification obligations are retained. -/
theorem weak_y_exists
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    ∃ y : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      FiniteDetected D 9 (by decide) 11 136 4 eY y ∧
      lambdaMultiply 2 (sphereAction h₀ y) ≠ 0 := by
  let SF := KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing
  obtain ⟨a11,ha⟩ := alpha_one_exists
  obtain ⟨z,hz⟩ := main_module_toda_nonempty_of_alpha D η h₀ ((L).U M) eV
    routeLiterature.toda.eta_squared a11 ha
  have unique := anyy_eta_unique_from_low_degrees routeLiterature.synthetic.eInfty
    sphereVanishing
    (KIP126.Main.Solution.Computation.sphere_eta_nonzero_unique KIP126.Main.StageInput.witness)
    (KIP126.Main.Solution.Computation.sphere_e2_two_three_subsingleton KIP126.Main.StageInput.witness)
  obtain ⟨t,ht,he,_⟩ := anyy_bracket_exact_target I SF
    routeLiterature.synthetic routeLiterature.realization unique η h₀
    routeLiterature.toda.eta_squared routeLiterature.toda.low_indeterminacy
    eV hc3 hc5 a11 ha z hz
  have hzn := weak_initial_twice_h0_nonzero I SF routeLiterature.synthetic.eInfty
    literature.bindings.route.algebra literature.bindings.route.quotientBinding
    literature.bindings.route.algebraBinding hc3 h₀ z t ht he
  obtain ⟨theta,hcriterion,_,_⟩ := routeLiterature.bx
  have htheta : ThetaChoice M (D).toModelData theta := hcriterion.2.1
  obtain ⟨b,zTheta,hb,hzTheta,hToda⟩ := synthetic_theta_b_toda theta htheta
  have hlabel := (I).products ⟨1,64,8,70⟩
    (by simp [KIP126.Computation.Route.Raw.products]) KIP126.LinE2.dataH6 KIP126.Computation.Near126.B
  dsimp only at hlabel
  rw [(I).labels.h6] at hlabel
  have hzTheta' : SphereDetected D 9 134 0
      ((I).realization.sphere 9 134
        (KIP126.LinE2.mulAt KIP126.LinE2.dataH6 KIP126.Computation.Near126.B)) zTheta := by
    rw [hlabel]
    exact hzTheta
  obtain ⟨y,hf,hn⟩ := main_weak_high_representative I routeLiterature.synthetic
    routeLiterature.realization SF classical_stem124_af13_generated
    η routeLiterature.classical.hopf.1 h₀ theta htheta b hb zTheta hzTheta'
    (theta_b_multiplied_shuffle theta htheta b zTheta hToda) z hzn
  have hy := weak_y_detected_from_low I routeLiterature.synthetic.eInfty
    literature.bindings.route.algebra literature.bindings.route.algebraBinding
    η routeLiterature.toda y hf hn
  exact ⟨y, hy, hn⟩

end
end KIP126.Main.Solution.Route.Section7
