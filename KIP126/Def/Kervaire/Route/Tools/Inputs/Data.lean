module

public import KIP126.Def.Kervaire.Route.SourceLanguage

@[expose] public section

/-! Mathematical premises for the generalized paper rules on one route model.
These packages assert neither their own existence nor any computed conclusion.
Source bindings and source-to-model assembly remain in Interface. The existing
public namespaces and all fields are retained during this relocation. -/

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- BHS A.9/A.11 with the compatible E∞ formulas on the SAME family.
All label, λ and ρ compatibility is part of the supplied source application.
No unrelated E∞ equivalences may be inserted as substitutes. -/
structure EInftyInput where
  presentation : KIP126.Literature.Route.EInftyFormulaInput D
  weightShift : EInftyWeightShift D.family
  maps : KIP126.Literature.Route.EInftyCompatibilityInput D presentation weightShift
  labels : KIP126.Literature.Route.EInftyLabelAgreement D presentation

/-- Applied mathematical comparisons on the same model. Literature delivery
must supply these premises; no rule conclusion is installed as a field. -/
structure SyntheticInputs where
  lifts : KIP126.Literature.Route.SyntheticLiftInput D
  finite_lift : FiniteLiftCriterion D
  bockstein : BocksteinDifferential D
  permanent_lift : PermanentLiftCriterion D
  differentials : DifferentialRigidity D
  eInfty : EInftyInput D
  realization_kernel : RealizationKernel D
  filtration_lambda : FiltrationLambda D
  e2_weight_vanishing : E2WeightVanishing D
  finite_quotient_page_vanishing : FiniteQuotientPageVanishing D

end
end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- Applied May input, retaining the source sign and the fixed conventions.
Consumers may remove the sign only after proving the required exponent-two
condition. Mod-two E₂ coordinates alone do not prove such a condition on
homotopy groups. -/
structure MayInput extends MayContext Syn where
  boundary : toMayContext.SignedBoundary

end KIP126.Literature.Route
