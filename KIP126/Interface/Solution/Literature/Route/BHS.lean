module

public import KIP126.Interface.Challenge.Challenge2
public import KIP126.Interface.Solution.Literature.Applications
public import KIP126.Def.StageInput.StandardSphere.Sequence.Proofs

@[expose] public section

/-! BHS source theorems, specialization and selected-to-completed comparison.

The source theorems are explicit unfinished proofs on Def's fixed synthetic
construction and its fixed realization coordinates. Their source-object
nilpotent-completeness and strong-convergence hypotheses remain explicit.

The source adapters below consume the delivered source statements and retain
the hypotheses of BHS A.1(2) and cor:tau-surj (Source/BHS/source/SynRevBigraded.tex
and SynRevAdams.tex). Finite Cλ lifting is intentionally separate.

The construction theorem uses bounded-below mod-two completion and the
finite-type sphere, its actual ν cofiber, the identified connective tmf,
and their shifts. The image and divisibility comparisons are internal
proof obligations. The standard classical sphere is specified as the derived
2-completion; its construction and applicability proofs remain unfinished. The generic
comparison language retains actual completion maps without identifying an
arbitrary selected object with its completion by definition.
No theorem in this file invokes the aggregate Challenge2 production target.
-/
namespace KIP126.Interface.Solution.Literature.Route
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.Literature.Route

/-- The actual selected ν cofiber has finite mod-two homology, by exact
tensoring of its sphere triangle. No Hopf detection or literature input is used. -/
theorem standard_nu_cofiber_finite_mod2_type :
    FiniteMod2Type standardFoundation.hf2
      (ClassicalObject.obj (C := standardFoundation.Spectrum)
        standardRouteModel.auxiliary .nuCofiber) := by
  let c := KIP126.Def.StageInput.witness
  letI : KIP126.Foundation.TensorInput c.foundationInput := c.tensorInput
  letI : (tensorLeft standardFoundation.hf2.HF2).CommShift ℤ :=
    KIP126.Foundation.TensorInput.leftShift (F := c.foundationInput) _
  letI : (tensorLeft standardFoundation.hf2.HF2).IsTriangulated :=
    KIP126.Foundation.TensorInput.leftExact (F := c.foundationInput) _
  have hs : FiniteMod2Type standardFoundation.hf2 SphereSpectrum :=
    KIP126.Def.standardSphereFiniteMod2Type
  exact FiniteMod2Type.of_cofiber
    (HoCofiberSequence.ofMorphism (C := standardFoundation.Spectrum)
      standardRouteModel.auxiliary.nuMap) (hs.shift 3) hs

/-- BHS A.1(1),(2), on Def's fixed synthetic construction. Clause (2)
gives a lift; restriction to every finite quotient and clause (1) give the
converse. Permanent cycles here may be boundaries or zero. -/
theorem bhs_permanent_lift_source
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X) :
    BHSPermanentLiftAt standardRouteModel X := by
  sorry

/-- BHS cor:tau-surj, on the same fixed construction. -/
theorem bhs_filtration_lambda_source
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X) :
    BHSFiltrationLambdaAt standardRouteModel X := by
  sorry

/-- BHS A.1(2a),(2b),(3a),(3b), using Def's fixed realization coordinates
and the canonical convergence identification of this same applicable X. -/
theorem bhs_realization_source
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X)
    (convergence : TowerDetection.Convergence standardFoundation.hf2.unit X) :
    BHSRealizationDetectionAt standardRouteModel
      KIP126.Def.standardRouteBackground.realization X convergence := by
  sorry

/-- Apply BHS `cor:synth-ctau-ASS` (1),(3) on the same supplied synthetic
family and positive finite lambda quotient. This projection retains all
finite pages r >= 2 and both weight inequalities. It does not derive an
E3 or E7 zero region from an E-infinity-only comparison, and it supplies no
new computation result. The source background must prove this field along
with its other BHS source statements. -/
theorem bhs_finite_quotient_page_vanishing
    (route : StandardRouteInput) (source : SyntheticSourceInputs route.model) :
    FiniteQuotientPageVanishing route.model :=
  source.finite_quotient_page_vanishing

/-- Apply BHS A.1(2) from the SAME delivered route source. Merely supplying
an abstract route does not establish the source theorem. Completeness and
strong convergence of the actual source tower remain explicit. -/
theorem bhs_permanent_lift_of_complete_source
    (route : StandardRouteInput) (source : SyntheticSourceInputs route.model)
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X) :
    BHSPermanentLiftAt route.model X :=
  source.permanent_lift X products hX

/-- BHS cor:tau-surj on that same source. -/
theorem bhs_filtration_lambda_of_complete_source
    (route : StandardRouteInput) (source : SyntheticSourceInputs route.model)
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X) :
    BHSFiltrationLambdaAt route.model X :=
  source.filtration_lambda X products hX

/-- Specialization consumes the SAME route source and the actual fixed
background proof. Only the classical sphere/HF₂ background is fixed in Def. -/
theorem standard_sphere_permanent_lift
    (route : StandardRouteInput) (source : SyntheticSourceInputs route.model) :
    BHSPermanentLiftAt route.model SphereSpectrum :=
  bhs_permanent_lift_of_complete_source route source _ _
    KIP126.Def.standardSphereApplicability

theorem standard_sphere_filtration_lambda
    (route : StandardRouteInput) (source : SyntheticSourceInputs route.model) :
    BHSFiltrationLambdaAt route.model SphereSpectrum :=
  bhs_filtration_lambda_of_complete_source route source _ _
    KIP126.Def.standardSphereApplicability

/-- The remaining untruncated clauses of BHS A.1 on an applicable source.
The classical convergence is canonical for that SAME source object's tower. -/
theorem bhs_realization_of_complete_source
    (route : StandardRouteInput)
    (R : RealizationCoordinates route.model)
    (source : BHSRealizationSourceResults route.model R)
    (X : standardFoundation.Spectrum)
    (products : HasProductsOfShape ℕ standardFoundation.Spectrum)
    (hX : BHSObjectApplicability products standardFoundation.hf2.unit X)
    (convergence : TowerDetection.Convergence standardFoundation.hf2.unit X) :
    BHSRealizationDetectionAt route.model R X convergence :=
  source X products hX convergence

section Transport
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Transport source lifetime/detection and the two existential lift clauses.
The hypotheses contain actual q/νq maps, canonical detection comparison,
realization naturality, and the precise prescribed/torsion image reflections.
The proof uses λ naturality and the source clauses; it never calls a paper
proposition, Challenge2, or a high125 conclusion. -/
theorem realization_detection_of_completed_sources
    (D : Model H M Syn) (R : RealizationCoordinates D) (Q : BHSCompletionData D)
    (source : BHSRealizationSourceResults D R)
    (applicable : BHSCompletionApplicability D Q)
    (comparison : BHSCompletionComparison D Q)
    (realization : BHSRealizationComparison D R Q) : RealizationDetection D R := by
  constructor
  · intro X s t r hr x a hx hs ha
    have h := (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).lifetime s t r hr
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
      (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
      ((comparison.permanent_cycles X s t x).mp hx)
      ((realization.survives_to X s t r x).mp hs)
      (realization.first_quotient_natural X s t x a ha)
    intro hz
    apply h
    simpa only [lambdaMultiply, Category.assoc, zero_comp] using
      congrArg (fun z => z ≫ (SyntheticCategory.biShift (0,0)).map
        (D.nu.functor.map (Q.map X))) hz
  · intro X s t x a hx ha
    apply (realization.detection X s t x (realizeNuZero D R X a)).mpr
    rw [realization.realization_natural]
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).detection s t
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
      (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
      ((realization.nonzero_survival X s t x).mp hx)
      (realization.first_quotient_natural X s t x a ha)
  · intro X s t x α hx hα
    apply realization.prescribed_lift_reflection X s t x α
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).prescribed_lift s t
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) x) (α ≫ Q.map X)
      ((realization.nonzero_survival X s t x).mp hx)
      ((realization.detection X s t x α).mp hα)
  · intro X s t r hr y hy hh
    apply realization.torsion_lift_reflection X s t (r-1) y
    exact (source (Q.completed X) Q.products (applicable.source X)
      (Q.convergence X)).boundary_lift s t r hr
      (adamsInternalE2Induced H.unit (Q.map X) (s,t) y)
      ((comparison.permanent_cycles X s t y).mp hy)
      ((realization.hit_on_page X s t r y).mp hh)
end Transport

/-- Choose actual completed sources and prove the comparisons needed to return
to the selected classical objects. Only connective and finite-mod-two-type
scope is needed from tmf; neither high125 nor its detection is a premise. B fixes the detector, its actual unit, and labels.
For `.nuCofiber`, the source of q is definitionally the cofiber of the SAME
D.auxiliary.nuMap; the proof uses completion of that cofiber and shift closure.

This internal producer constructs Q and its comparisons. In the selected
HF₂-local classical category the chosen sphere, finite Hopf cofiber and
connective finite-type detector are already local; the identity comparison
is available after their nilpotent-completeness and convergence are proved.
No source theorem is inferred for an arbitrary synthetic category here.
This parameterized construction is broader than the fixed literature delivery;
it is retained as an internal helper, not a second fixed-model acceptance goal.
Projecting the fixed delivery's completion fields cannot prove this statement
for arbitrary `route` and `R`. -/
theorem bhs_completed_sources
    (route : StandardRouteInput)
    (R : RealizationCoordinates route.model)
    (G : TmfLabels standardFoundation.hf2)
    (S : TmfSourceData standardFoundation.hf2)
    (connective : ∀ n : ℤ, n < 0 →
      Subsingleton (HomotopyGroup n S.spectrum))
    (finiteMod2Type : FiniteMod2Type standardFoundation.hf2 S.spectrum)
    (B : TmfBinding route.model G S) :
    ∃ Q : BHSCompletionData route.model,
      BHSCompletionApplicability route.model Q ∧
      BHSCompletionComparison route.model Q ∧
      BHSRealizationComparison route.model R Q ∧
      ∃ e : Q.completed .detector ≅ S.spectrum,
        route.model.auxiliary.detectorUnit ≫ Q.map .detector ≫ e.hom = S.unit := by
  sorry

end KIP126.Interface.Solution.Literature.Route
