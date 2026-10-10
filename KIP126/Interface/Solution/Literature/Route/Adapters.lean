import KIP126.Interface.Solution.Literature.Route.BHS
import KIP126.Interface.Solution.Literature.Route.Moss
import KIP126.Interface.Solution.Literature.Route.RealizationKernel
import KIP126.Interface.Solution.Literature.Route.Toda
import KIP126.Interface.Solution.Literature.Route.May
import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

namespace KIP126.Interface.Solution.Literature.Route
open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Core.SpectralSequence
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.Literature.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

set_option backward.isDefEq.respectTransparency false in
/-- Transport a compatible source triple along the three ACTUAL map equalities.
No statement is made about arbitrary normalized lifts. -/
theorem nuCofiber_of_source (S : NuCofiberSourceData D)
    (hS : NuCofiberSourceResults D S) (B : NuCofiberLiftBinding D S) :
    NuCofiberApplicability D := by
  refine ⟨hS.nu_exponent, hS.bottom_exponent, hS.top_exponent, ?_, ?_⟩
  · simpa [sourceNormalizedNu, normalizedNu, B.nu] using hS.normalized_label
  · intro he
    change normalizedTriangle D.toModelData D.auxiliary.nuRouteTriangle he ∈ distTriang Syn
    have h := hS.triangle he
    convert h using 1
    simp [normalizedTriangle, sourceNormalizedTriangle, normalizedConnecting,
        sourceNormalizedConnecting, AuxiliaryData.nuRouteTriangle,
        B.nu, B.bottom, B.top]

/-- Assemble source transports on the SAME bindings. The secondary Toda
comparison, completed-source comparisons and compatible lift triple remain explicit
producer premises; source names alone do not establish those comparisons.
The tmf leading-grade survival deduction is not an Interface delivery. -/
theorem application_of_parts (η : BiHom 1 2 (S_0_0 : Syn)) (G : TmfLabels H)
    {background : Background D} (B : Bindings D η G background) (A : Statements D η G B)
    (hBHS : BHSCompletionApplicability D B.bhsCompletion)
    (cBHS : BHSCompletionComparison D B.bhsCompletion)
    (rBHS : BHSRealizationComparison D B.realization B.bhsCompletion)
    (secondary : TodaSecondaryComparison η B.todaSource)
    (hnu : NuCofiberSourceResults D B.nuSource) : Application D η G B := by
  exact ⟨hBHS, cBHS,
    realization_detection_of_completed_sources D B.realization B.bhsCompletion
      A.realization hBHS cBHS rBHS,
    may_signed_boundary_of_source B.may A.may,
    todaApplication_of_secondary η B.todaSource secondary,
    realizationKernel_of_source D B.kernelSource A.realizationKernel B.kernelBinding,
    mossInputOfClassicalSource D η B.classicalSource B.classicalBinding A.moss,
    hnu, nuCofiber_of_source D B.nuSource hnu B.nuBinding⟩

end
end KIP126.Interface.Solution.Literature.Route

/-! Assemble the same literature fields with explicitly supplied internal
Moss specialization and weight-shift naturality. Main proves those two
applications; the Interface producer does not depend on Main. -/
namespace KIP126.Challenge2.LiteratureResults
open CategoryTheory Classical.Adams Core.SpectralSequence
open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open KIP126.Literature.Route
variable {bindings : KIP126.Challenge2.LiteratureBindings}

noncomputable def route (input : LiteratureResults bindings)
    (localMoss : MossSourceInput standardMilnorCooperations
      bindings.route.classicalSource.convergence)
    (shiftNatural : bindings.eInftyWeightShift.Natural) :
    Literature.Route.Statements standardRouteModel Def.standardRouteEta
      bindings.tmfLabels bindings.route where
  classical := {
    h5Square_permanent := input.classical_h5Square_permanent
    theta5_detection := input.classical_theta5_detection
    theta5_order_two := input.classical_theta5_order_two
    stem62_exponent_two := input.classical_stem62_exponent_two
    theta5_filtration_gap := input.classical_theta5_filtration_gap
    two_detection := input.classical_two_detection
    eta_detection := input.classical_eta_detection
    nu_detection := input.classical_nu_detection
    eta_permanent := input.classical_eta_permanent
    nu_permanent := input.classical_nu_permanent
  }
  bx := input.route_bx
  synthetic := {
    lifts := {
      nu_cofiber := input.synthetic_nu_cofiber
      lift := input.synthetic_lift
      triangle_lift := input.synthetic_triangle_lift
    }
    finite_lift := input.synthetic_finite_lift
    bockstein := input.synthetic_bockstein
    permanent_lift := input.synthetic_permanent_lift
    differentials := input.synthetic_differentials
    filtration_lambda := input.synthetic_filtration_lambda
    e2_weight_vanishing := input.synthetic_e2_weight_vanishing
    finite_quotient_page_vanishing := input.synthetic_finite_quotient_page_vanishing
    eInfty := {
      presentation := bindings.eInftyPresentation
      weightShift := bindings.eInftyWeightShift
      maps := {
        shift_natural := shiftNatural
        lambda_nu := input.eInfty_lambda_nu
        lambda_finite := input.eInfty_lambda_finite
        rho_finite := input.eInfty_rho_finite
        rho_nu := input.eInfty_rho_nu
      }
      labels := input.eInfty_labels
    }
  }
  realizationKernel := input.route_realizationKernel
  realization := by
    intro X products applicability convergence
    exact {
      lifetime := input.realization_lifetime X products applicability convergence
      detection := input.realization_detection X products applicability convergence
      prescribed_lift := input.realization_prescribed_lift X products applicability convergence
      boundary_lift := input.realization_boundary_lift X products applicability convergence
    }
  may := input.route_may
  toda := {
    h0_label := input.toda_h0_label
    lambda_h0 := input.toda_lambda_h0
    h0_eta := input.toda_h0_eta
    low_indeterminacy := input.toda_low_indeterminacy
  }
  tmf := {
    connective := input.tmf_connective
    finiteMod2Type := input.tmf_finiteMod2Type
    standard_labels := input.tmf_standard_labels
    vanishing62 := input.tmf_vanishing62
    low_filtration63 := input.tmf_low_filtration63
    kappaBar_detection := input.tmf_kappaBar_detection
    w_detection := input.tmf_w_detection
    high125_nonzero := input.tmf_high125_nonzero
  }
  moss := localMoss


end KIP126.Challenge2.LiteratureResults
