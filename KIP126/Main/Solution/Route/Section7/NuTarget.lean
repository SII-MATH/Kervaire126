module

import KIP126.Main.Solution.Route.Section7.ProofSupport

public import KIP126.Main.Solution.Route.Section7.Common
import KIP126.Main.Solution.Route.Section7.WeakY
import KIP126.Main.Solution.Route.Section7.NuNinth
import Batteries.Tactic.OpenPrivate

-- The P/Q lifting proof belongs to the M18 implementation.
import all KIP126.Main.Solution.Route.Section7.NuTargetHelpers

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

open private nu_target_full_of_nonzero
  from KIP126.Main.Solution.Route.Section7.NuTargetHelpers

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- `prop:state5false`: consume the joint weak-representative handoff, then
apply the actual ninth-quotient nu extension and the P/Q lifting argument. -/
theorem target_nu_divisible
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    TargetNuDivisible D ((L).target M) h2 := by
  let SF := KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing
  obtain ⟨y, hy, hn⟩ := weak_y_exists hc3 hc5
  exact nu_target_full_of_nonzero I routeLiterature.synthetic SF
    literature.bindings.route.algebra literature.bindings.route.quotientBinding
    literature.bindings.route.algebraBinding h2
    routeLiterature.applicability.nuCofiber.normalized_label h₀
    routeLiterature.toda.h0_label routeLiterature.toda.lambda_h0
    nu_extension_in_ninth_quotient y hy.1 hn

end
end KIP126.Main.Solution.Route.Section7
